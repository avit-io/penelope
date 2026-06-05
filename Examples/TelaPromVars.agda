{-# OPTIONS --safe --without-K #-}

module Examples.TelaPromVars where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  TelaPromVars — riproduzione di panel-47 di BeAccount come panel   ║
-- ║  Prometheus (HenQL) `status-history`:                              ║
-- ║                                                                    ║
-- ║    sum by (Name) (                                                 ║
-- ║      changes(                                                      ║
-- ║        health_checks_count{ SourceService="BeAccounts"             ║
-- ║                           , Env=~"$env"                            ║
-- ║                           , Status="FAIL" }[$__interval]))         ║
-- ║                                                                    ║
-- ║  Il riferimento `Env =ᵛ env` si interpola FEDELMENTE come          ║
-- ║  `Env=~"$env"` perché `env.multi = true` (Grafana sostituisce      ║
-- ║  `v₁|v₂` con regex → disgiunzione esatta).                         ║
-- ║                                                                    ║
-- ║  La Variable `env` è dichiarata con `sourceGrafanaType =           ║
-- ║  "elasticsearch"`: è la dashboard variable che vive lato Grafana   ║
-- ║  come terms-query su `Env.keyword`. Nei panel Prometheus non c'è   ║
-- ║  garanzia di esistenza della label (le label PromQL sono APERTE);  ║
-- ║  il matcher è solo ben formato sul nome.                            ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Prometea.Core
open import HenQL.Syntax            using (Expr; metricSel; rangeS; changes;
                                            sumBy; Matcher; mkMatcher; meq)
open import HenQL.Print             using (prettyExpr)

open import Penelope.Panel
open import Penelope.Datasource
open import Penelope.Backend.Prometheus
open import Penelope.Tiling
open import Penelope.Dashboard
open import Penelope.JSON
open import Penelope.Sugar
open import Penelope.Variable       using (Variable; mkQueryVariable)

open import Data.Nat                using (ℕ)
open import Data.Float              using (Float)
open import Data.Bool               using (true; false)
open import Data.String             using (String)
open import Data.List               using (List; _∷_; [])
open import Data.List.NonEmpty      using (_∷_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

-- ── Modello concreto ─────────────────────────────────────────────────
beModel : Model
beModel = record { Time = ℕ ; Val = Float ; Series = String }

promBE : Datasource
promBE = prometheus beModel

-- ── Variable `env`: terms su `Env.keyword`, lato Elastic, multi+all.
-- ── (Stessa dichiarazione che useranno i panel ES in TelaCondivisa.)
envVar : Variable
envVar = mkQueryVariable "env" "elasticsearch" "Env.keyword" true true

-- ── Matchers PromQL del selettore: 3 voci, di cui una a variabile. ──
healthMatchers : List (Matcher beModel)
healthMatchers =
    mkMatcher "SourceService" meq "BeAccounts"
  ∷ ("Env" =ᵛ envVar)
  ∷ mkMatcher "Status"        meq "FAIL"
  ∷ []

-- ── L'Expr PromQL: sum by (Name) (changes(health[$__interval])). ────
panel47Expr : Expr beModel InstantVector
panel47Expr =
  sumBy ("Name" ∷ [])
    (changes
      (rangeS "health_checks_count" healthMatchers "$__interval"))

-- ── Il panel `status-history` con UN target e Panel.vars = [envVar]. ─
panel-47 : Panel promBE StatusHistory
panel-47 = record
  { title   = "Health by Source"
  ; targets = mkTarget panel47Expr nothing false tt ∷ []
  ; vars    = envVar ∷ []
  }
  where
    open import Data.Maybe using (nothing)
    open import Data.Unit  using (tt)

-- ── Dashboard 24×8 con un solo panel. ────────────────────────────────
viewport : Rect
viewport = mkRect 0 0 24 8

tela : TilingOf AnyPanel viewport
tela = tile (□ panel-47)

promVarsDash : Dashboard
promVarsDash = mkDashboard "BeAccount — panel-47" "beaccount-47"
                           [] viewport tela

json : String
json = renderDashboard promVarsDash

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Goldens refl                                                       ║
-- ╚════════════════════════════════════════════════════════════════════╝

-- (a) La PromQL emessa contiene `Env=~"$env"` (multi → `=~`) e
-- `[$__interval]` come finestra.
_ : Datasource.render promBE panel47Expr
  ≡ "sum by (Name) (changes(health_checks_count{SourceService=\"BeAccounts\",Env=~\"$env\",Status=\"FAIL\"}[$__interval]))"
_ = refl

-- (b) Il blocco `variables` deriva dalla `Panel.vars` del solo panel:
-- una sola `env`.
_ : dashboardVariables promVarsDash ≡ envVar ∷ []
_ = refl
