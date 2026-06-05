{-# OPTIONS --safe --without-K #-}

module Examples.TelaMulti where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  TelaMulti — un singolo panel con TRE target sullo stesso          ║
-- ║  datasource (elastic), riproduzione di panel-12 della dashboard    ║
-- ║  BeAccount:                                                        ║
-- ║   A  alias "INFO",  count, Source=Activity ∧ Level=INFO  ∧ Env=…   ║
-- ║   B  alias "ERROR", count, Source=Activity ∧ Level=ERROR ∧ Env=…   ║
-- ║   C  hidden true,   count, …=ERROR ∧ ¬StatusCode=404 ∧ ¬…=401      ║
-- ║                                                                    ║
-- ║  env è un PARAMETRO della definizione (non una variabile di        ║
-- ║  dashboard — quelle arrivano nel prossimo Tier 1).                 ║
-- ║                                                                    ║
-- ║  La fedeltà al frammento Elastic vale PER OGNI target (filtri      ║
-- ║  booleani su `var ≡ lit` su TStr, con `¬ᵉ` sopra): faithfulElastic ║
-- ║  riduce a `true` per costruzione, quindi `ok = tt`.                ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Loquel.Schema       using (Schema; TStr)
open import Loquel.Expr         using (var; lit; _≡ᵉ_; _∧ᵉ_; ¬ᵉ_)
open import Loquel.Pipe         using (Pipe; filterp)
open import Loquel.Render.LogQL using (MetricKind; MCount)

open import Data.List.Membership.Propositional        using (_∈_)
open import Data.List.Relation.Unary.Any              using (here; there)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Data.Unit                                  using (tt)

open import Penelope.Panel
open import Penelope.Datasource
open import Penelope.Backend.Loquel
open import Penelope.Tiling
open import Penelope.Dashboard
open import Penelope.JSON
open import Penelope.Sugar

open import Data.Bool          using (false; true)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.String        using (String)
open import Data.Product       using (_,_)
open import Data.List          using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; head; tail) renaming (_∷_ to _∷⁺_)

-- ── Schema BeAccount (campi rilevanti per panel-12) ──────────────────
beSchema : Schema
beSchema = ("Source"               , TStr)
         ∷ ("LoggerLevel.keyword"  , TStr)
         ∷ ("Env"                  , TStr)
         ∷ ("StatusCode"           , TStr)
         ∷ []

source∈ : ("Source" , TStr)              ∈ beSchema
source∈ = here refl
level∈  : ("LoggerLevel.keyword" , TStr) ∈ beSchema
level∈  = there (here refl)
env∈    : ("Env" , TStr)                 ∈ beSchema
env∈    = there (there (here refl))
status∈ : ("StatusCode" , TStr)          ∈ beSchema
status∈ = there (there (there (here refl)))

-- ── Datasource Elastic per BeAccount ─────────────────────────────────
elasticDS : Datasource
elasticDS = elastic beSchema

-- ── I tre filtri (parametrizzati su `env`) ───────────────────────────
infoPipe : String → Pipe beSchema beSchema
infoPipe e = filterp
  ( (var source∈ ≡ᵉ lit "Activity")
  ∧ᵉ (var level∈  ≡ᵉ lit "INFO")
  ∧ᵉ (var env∈    ≡ᵉ lit e) )

errorPipe : String → Pipe beSchema beSchema
errorPipe e = filterp
  ( (var source∈ ≡ᵉ lit "Activity")
  ∧ᵉ (var level∈  ≡ᵉ lit "ERROR")
  ∧ᵉ (var env∈    ≡ᵉ lit e) )

errorNoExpectedPipe : String → Pipe beSchema beSchema
errorNoExpectedPipe e = filterp
  ( (var source∈ ≡ᵉ lit "Activity")
  ∧ᵉ (var level∈  ≡ᵉ lit "ERROR")
  ∧ᵉ (var env∈    ≡ᵉ lit e)
  ∧ᵉ (¬ᵉ (var status∈ ≡ᵉ lit "404"))
  ∧ᵉ (¬ᵉ (var status∈ ≡ᵉ lit "401")) )

-- ── Il panel: TimeSeries su elastic con tre Target ───────────────────
-- queryTypeOf TimeSeries = rangeM, quindi il target è `rangeT pipe …`.
-- Su elastic, renderElasticS ignora MetricKind/window e usa solo la
-- pipe; restano comunque obbligatori dal tipo di rangeT.

-- I tre target nominati: ognuno è funzione di env, così le goldens
-- referenziano gli stessi termini che entrano nel panel.

infoTarget : String → Target elasticDS TimeSeries
infoTarget e = mkTarget (rangeT (infoPipe e) MCount [] "5m")
                        (just "INFO") false tt

errorTarget : String → Target elasticDS TimeSeries
errorTarget e = mkTarget (rangeT (errorPipe e) MCount [] "5m")
                         (just "ERROR") false tt

errorNoExpTarget : String → Target elasticDS TimeSeries
errorNoExpTarget e = mkTarget (rangeT (errorNoExpectedPipe e) MCount [] "5m")
                              nothing true tt

panel-12 : String → Panel elasticDS TimeSeries
panel-12 e = record
  { title   = "Activity by level"
  ; targets = infoTarget e ∷⁺ errorTarget e ∷ errorNoExpTarget e ∷ []
  ; vars    = []
  }

-- ── Dashboard con un solo panel 24×8 ─────────────────────────────────
viewport : Rect
viewport = mkRect 0 0 24 8

tela : TilingOf AnyPanel viewport
tela = tile (□ (panel-12 "prod"))

multiDash : Dashboard
multiDash = mkDashboard "BeAccount — panel-12" "beaccount-12"
                        [] viewport tela

json : String
json = renderDashboard multiDash

-- ── Golden refl: i target del panel-12 sono esattamente i tre nominati.
_ : Panel.targets (panel-12 "prod")
  ≡ infoTarget "prod" ∷⁺ errorTarget "prod" ∷ errorNoExpTarget "prod" ∷ []
_ = refl

-- A: alias "INFO", hidden false, expr Elastic.
_ : Target.alias  (infoTarget "prod") ≡ just "INFO"
_ = refl
_ : Target.hidden (infoTarget "prod") ≡ false
_ = refl
_ : Datasource.render elasticDS (Target.query (infoTarget "prod"))
  ≡ "{\"query\":{\"bool\":{\"must\":[{\"term\":{\"Source\":\"Activity\"}},{\"bool\":{\"must\":[{\"term\":{\"LoggerLevel.keyword\":\"INFO\"}},{\"term\":{\"Env\":\"prod\"}}]}}]}}}"
_ = refl

-- B: alias "ERROR", hidden false.
_ : Target.alias  (errorTarget "prod") ≡ just "ERROR"
_ = refl
_ : Target.hidden (errorTarget "prod") ≡ false
_ = refl
_ : Datasource.render elasticDS (Target.query (errorTarget "prod"))
  ≡ "{\"query\":{\"bool\":{\"must\":[{\"term\":{\"Source\":\"Activity\"}},{\"bool\":{\"must\":[{\"term\":{\"LoggerLevel.keyword\":\"ERROR\"}},{\"term\":{\"Env\":\"prod\"}}]}}]}}}"
_ = refl

-- C: nessun alias, hidden true.
_ : Target.alias  (errorNoExpTarget "prod") ≡ nothing
_ = refl
_ : Target.hidden (errorNoExpTarget "prod") ≡ true
_ = refl
_ : Datasource.render elasticDS (Target.query (errorNoExpTarget "prod"))
  ≡ "{\"query\":{\"bool\":{\"must\":[{\"term\":{\"Source\":\"Activity\"}},{\"bool\":{\"must\":[{\"term\":{\"LoggerLevel.keyword\":\"ERROR\"}},{\"bool\":{\"must\":[{\"term\":{\"Env\":\"prod\"}},{\"bool\":{\"must\":[{\"bool\":{\"must_not\":[{\"term\":{\"StatusCode\":\"404\"}}]}},{\"bool\":{\"must_not\":[{\"term\":{\"StatusCode\":\"401\"}}]}}]}}]}}]}}]}}}"
_ = refl

-- ── Test negativo (documentato) ─────────────────────────────────────
--
-- Una pipe che proietta o usa parse su un campo diverso da "line" NON
-- sta nel frammento fedele Elastic — il typecheck rifiuta il Target:
--
--   bad : Target elasticDS TimeSeries
--   bad = mkTarget (rangeT (project _) MCount [] "5m") nothing false tt
--   -- ✗ tt ha tipo ⊤, ma `ok` chiede T (faithfulElasticB (project _))
--   --   = T false ≡ ⊥
