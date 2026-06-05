{-# OPTIONS --safe --without-K #-}

module Examples.TelaCondivisa where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  TelaCondivisa — una variabile `env` REFERENZIATA da entrambi i    ║
-- ║  backend nella stessa dashboard:                                    ║
-- ║                                                                    ║
-- ║   • panel ES (Loquel)        : filtro `Env.keyword ==ᵛ env`;       ║
-- ║   • panel Prometheus (HenQL) : matcher  `Env =ᵛ env`.              ║
-- ║                                                                    ║
-- ║  La derivazione del blocco `variables` è BACKEND-AGNOSTICA: walka  ║
-- ║  la tela, raccoglie Panel.vars dai due panel (entrambi contengono  ║
-- ║  la STESSA `envVar`), dedupplica per nome → UNA sola voce nel      ║
-- ║  templating.                                                       ║
-- ║                                                                    ║
-- ║  Test negativo (documentato a fine file): due dichiarazioni di     ║
-- ║  `env` con `multi` discordanti NON typeckecka — la well-formedness ║
-- ║  della Dashboard riduce a `T false ≡ ⊥`.                           ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Loquel.Schema       using (Schema; TStr)
open import Loquel.Expr         using (var; lit; _≡ᵉ_; _∧ᵉ_)
open import Loquel.Pipe         using (Pipe; filterp)
open import Loquel.Render.LogQL using (MetricKind; MCount)

open import Data.List.Membership.Propositional        using (_∈_)
open import Data.List.Relation.Unary.Any              using (here; there)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Data.Unit                                  using (tt)

open import Prometea.Core           using (Model; PromType; InstantVector)
open import HenQL.Syntax            using (Expr; metricSel; rangeS; changes;
                                            sumBy; Matcher; mkMatcher; meq)

open import Penelope.Panel
open import Penelope.Datasource
open import Penelope.Backend.Loquel
open import Penelope.Backend.Prometheus
open import Penelope.Tiling
open import Penelope.Dashboard
open import Penelope.JSON
open import Penelope.Sugar
open import Penelope.Variable       using (Variable; mkQueryVariable)

open import Data.Nat                using (ℕ)
open import Data.Float              using (Float)
open import Data.Bool               using (true; false)
open import Data.Maybe              using (Maybe; just; nothing)
open import Data.String             using (String)
open import Data.Product            using (_,_)
open import Data.List               using (List; _∷_; [])
open import Data.List.NonEmpty      using (_∷_)

-- ╔══════════════════════ Variabile condivisa ════════════════════════╗
envVar : Variable
envVar = mkQueryVariable "env" "elasticsearch" "Env.keyword" true true

-- ╔══════════════════════ Lato Elastic (Loquel) ══════════════════════╗
beSchema : Schema
beSchema = ("Source"              , TStr)
         ∷ ("Env.keyword"         , TStr)
         ∷ []

source∈ : ("Source" , TStr)       ∈ beSchema
source∈ = here refl
env∈    : ("Env.keyword" , TStr)  ∈ beSchema
env∈    = there (here refl)

elasticDS : Datasource
elasticDS = elastic beSchema

envVar-loquel : Var beSchema
envVar-loquel = mkVar "env" "Env.keyword" env∈ true true

esPipe : Pipe beSchema beSchema
esPipe = filterp ((var source∈ ≡ᵉ lit "Activity") ∧ᵉ (env∈ ==ᵛ envVar-loquel))

esTarget : Target elasticDS TimeSeries
esTarget = mkTarget (rangeT esPipe MCount [] "5m") (just "ES") false tt

esPanel : Panel elasticDS TimeSeries
esPanel = record
  { title   = "Activity (ES) scoped by env"
  ; targets = esTarget ∷ []
  ; vars    = envVar ∷ []
  }

-- ╔════════════════════ Lato Prometheus (HenQL) ══════════════════════╗
beModel : Model
beModel = record { Time = ℕ ; Val = Float ; Series = String }

promDS : Datasource
promDS = prometheus beModel

promExpr : Expr beModel InstantVector
promExpr =
  sumBy ("Name" ∷ [])
    (changes
      (rangeS "health_checks_count"
              (("Env" =ᵛ envVar) ∷ mkMatcher "Status" meq "FAIL" ∷ [])
              "$__interval"))

promPanel : Panel promDS StatusHistory
promPanel = record
  { title   = "Health (Prom) by Name, scoped by env"
  ; targets = mkTarget promExpr nothing false tt ∷ []
  ; vars    = envVar ∷ []
  }

-- ╔══════════════════════ Tela 24×16 (ES ↕ Prom) ═════════════════════╗
viewport : Rect
viewport = mkRect 0 0 24 16

tela : TilingOf AnyPanel viewport
tela = top ↕ bot
  where
    top : Tiling AnyPanel 0 0 24 8
    top = tile (□ esPanel)
    bot : Tiling AnyPanel 0 8 24 8
    bot = tile (□ promPanel)

condivisa : Dashboard
condivisa = mkDashboard "BeAccount — condivisa" "beaccount-condivisa"
                        [] viewport tela

json : String
json = renderDashboard condivisa

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Goldens refl                                                       ║
-- ╚════════════════════════════════════════════════════════════════════╝

-- (a) DUE panel referenziano `env`, ma dopo dedup il blocco variables
-- ne contiene UNA sola.
_ : dashboardVariables condivisa ≡ envVar ∷ []
_ = refl

-- (b) Lato ES: la query Elastic emessa contiene il sentinella `$env`
-- sul campo `.keyword`.
_ : Datasource.render elasticDS (Target.query esTarget)
  ≡ "{\"query\":{\"bool\":{\"must\":[{\"term\":{\"Source\":\"Activity\"}},{\"term\":{\"Env.keyword\":\"$env\"}}]}}}"
_ = refl

-- (c) Lato Prom: la PromQL emessa contiene `Env=~"$env"`.
_ : Datasource.render promDS promExpr
  ≡ "sum by (Name) (changes(health_checks_count{Env=~\"$env\",Status=\"FAIL\"}[$__interval]))"
_ = refl

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Test negativo (documentato)                                       ║
-- ║                                                                    ║
-- ║  Due dichiarazioni con lo stesso `name` ma `multi` divergenti       ║
-- ║  fanno fallire la well-formedness della Dashboard:                 ║
-- ║                                                                    ║
-- ║    envVar2 : Variable                                              ║
-- ║    envVar2 = mkQueryVariable "env" "elasticsearch"                 ║
-- ║                              "Env.keyword" false true              ║
-- ║                                                                    ║
-- ║  Mettere `envVar` e `envVar2` come Panel.vars di due panel della   ║
-- ║  stessa tela ⇒ `varsConsistentB` riduce a `false` ⇒ il meta `wf`   ║
-- ║  di `mkDashboard` non si risolve (T false ≡ ⊥).                   ║
-- ╚════════════════════════════════════════════════════════════════════╝
