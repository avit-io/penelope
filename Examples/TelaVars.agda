{-# OPTIONS --safe --without-K #-}

module Examples.TelaVars where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  TelaVars — variabili di dashboard come riferimenti TIPATI dentro  ║
-- ║  le query Loquel.                                                  ║
-- ║                                                                    ║
-- ║  Un panel TimeSeries su `elastic` con un target il cui filtro      ║
-- ║  referenzia due variabili via `_==ᵛ_`:                             ║
-- ║   • $env         → Env.keyword         (multi, includeAll)         ║
-- ║   • $loggerlevel → LoggerLevel.keyword (multi, includeAll)         ║
-- ║                                                                    ║
-- ║  Il blocco `variables` del JSON si DERIVA dai riferimenti: la      ║
-- ║  dashboard non dichiara le variabili a mano, la collezione walka   ║
-- ║  la tela e raccoglie i `Panel.vars` (dedup per `name`).            ║
-- ║                                                                    ║
-- ║  Test negativi (documentati a fine file):                          ║
-- ║   1. `Var s` su un campo NON nello schema → errore di tipo;        ║
-- ║   2. `Var s` su un campo non-`.keyword` (testo libero) → errore.   ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Loquel.Schema       using (Schema; TStr)
open import Loquel.Expr         using (var; lit; _≡ᵉ_; _∧ᵉ_)
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
open import Data.List.NonEmpty using (List⁺) renaming (_∷_ to _∷⁺_)

-- ── Schema con campi `.keyword` (tokenizzati esatti) + un campo di
-- ── testo libero "line" (per il test negativo 2).
beSchema : Schema
beSchema = ("Source"               , TStr)
         ∷ ("LoggerLevel.keyword"  , TStr)
         ∷ ("Env.keyword"          , TStr)
         ∷ ("line"                 , TStr)
         ∷ []

source∈ : ("Source" , TStr)              ∈ beSchema
source∈ = here refl
level∈  : ("LoggerLevel.keyword" , TStr) ∈ beSchema
level∈  = there (here refl)
env∈    : ("Env.keyword" , TStr)         ∈ beSchema
env∈    = there (there (here refl))
line∈   : ("line" , TStr)                ∈ beSchema
line∈   = there (there (there (here refl)))

-- ── Datasource Elastic
elasticDS : Datasource
elasticDS = elastic beSchema

-- ── Variabili tipate, ancorate ai campi `.keyword` dello schema.
envVar : Var beSchema
envVar = mkVar "env" "Env.keyword" env∈ true true

levelVar : Var beSchema
levelVar = mkVar "loggerlevel" "LoggerLevel.keyword" level∈ true true

-- ── Filtro con `_==ᵛ_`: scope BeAccount (Source=Activity ∧ level ∧ env)
-- ── ma con `level` e `env` resi come sentinella `$loggerlevel`/`$env`.
basePipe : Pipe beSchema beSchema
basePipe = filterp
  ( (var source∈ ≡ᵉ lit "Activity")
  ∧ᵉ (level∈ ==ᵛ levelVar)
  ∧ᵉ (env∈   ==ᵛ envVar) )

-- ── Un target singolo (alias "ALL", visibile).
mainTarget : Target elasticDS TimeSeries
mainTarget = mkTarget (rangeT basePipe MCount [] "5m")
                      (just "ALL") false tt

-- ── Il panel registra le Var referenziate in `vars`. Sono opache qui:
-- ── `Variable` lato Penelope = `name + spec` (custom/query). Il JSON
-- ── renderer ne emette un QueryVariable a testa.
mainPanel : Panel elasticDS TimeSeries
mainPanel = record
  { title   = "Activity scoped"
  ; targets = mainTarget ∷⁺ []
  ; vars    = varToVariable levelVar ∷ varToVariable envVar ∷ []
  }

-- ── Una tela 24×8 con un solo panel.
viewport : Rect
viewport = mkRect 0 0 24 8

tela : TilingOf AnyPanel viewport
tela = tile (□ mainPanel)

-- ── Dashboard: niente `extraVars` (lista vuota); il blocco templating
-- ── si DERIVA interamente dai riferimenti dei panel.
varsDash : Dashboard
varsDash = mkDashboard "BeAccount — vars" "beaccount-vars" [] viewport tela

json : String
json = renderDashboard varsDash

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Goldens refl                                                       ║
-- ╚════════════════════════════════════════════════════════════════════╝

-- (a) La query Elastic emessa contiene `$env` e `$loggerlevel` sui
-- campi `.keyword` corretti. La forma right-assoc di `_∧ᵉ_` produce
-- un bool.must annidato.
_ : Datasource.render elasticDS (Target.query mainTarget)
  ≡ "{\"query\":{\"bool\":{\"must\":[{\"term\":{\"Source\":\"Activity\"}},{\"bool\":{\"must\":[{\"term\":{\"LoggerLevel.keyword\":\"$loggerlevel\"}},{\"term\":{\"Env.keyword\":\"$env\"}}]}}]}}}"
_ = refl

-- (b) Il blocco `variables` della dashboard è DERIVATO dai riferimenti
-- nei panel: due QueryVariable, una per `loggerlevel` (Env.keyword
-- field) e una per `env` (Env.keyword field), nello stesso ordine in
-- cui compaiono in `Panel.vars`.
_ : dashboardVariables varsDash
  ≡ varToVariable levelVar ∷ varToVariable envVar ∷ []
_ = refl

-- (c) `varToVariable` di una `Var` produce una `Variable` opaca con
-- spec `querySpec` sul campo `.keyword` corretto.
open import Penelope.Variable using (Variable; mkQueryVariable)

_ : varToVariable envVar ≡ mkQueryVariable "env" "Env.keyword" true true
_ = refl

_ : varToVariable levelVar ≡ mkQueryVariable "loggerlevel" "LoggerLevel.keyword" true true
_ = refl

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Test negativi (documentati)                                       ║
-- ║                                                                    ║
-- ║  1. Una `Var s` su un campo non nello schema non typeckecka — il   ║
-- ║     campo `fieldProof` di tipo `(fieldName , TStr) ∈ s` non è      ║
-- ║     costruibile:                                                   ║
-- ║                                                                    ║
-- ║       badField : Var beSchema                                      ║
-- ║       badField = mkVar "x" "NonEsiste" ???? true true              ║
-- ║       -- ✗ nessun proof `("NonEsiste" , TStr) ∈ beSchema`          ║
-- ║                                                                    ║
-- ║  2. Una `Var s` su un campo che NON termina in `.keyword` non      ║
-- ║     typeckecka — l'implicito `keywordOK : T (endsKeyword fld)`     ║
-- ║     riduce a `T false ≡ ⊥`:                                        ║
-- ║                                                                    ║
-- ║       badText : Var beSchema                                       ║
-- ║       badText = mkVar "txt" "line" line∈ true true                 ║
-- ║       -- ✗ nessun valore di T false                                ║
-- ╚════════════════════════════════════════════════════════════════════╝
