{-# OPTIONS --safe --without-K #-}

module Penelope.Variable where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Template variables — placeholder che Grafana sostituisce a        ║
-- ║  runtime per parametrizzare le query.                              ║
-- ║                                                                    ║
-- ║  Due forme:                                                        ║
-- ║   • customSpec : lista esplicita di valori ("custom") + flag       ║
-- ║                  multi/includeAll come le query-variable.          ║
-- ║   • querySpec  : terms-query su un campo + flag multi/includeAll   ║
-- ║                  ("query"). Porta anche `sourceGrafanaType` (es.    ║
-- ║                  "elasticsearch") perché Grafana richiede di        ║
-- ║                  associare la query-variable a un datasource: è il ║
-- ║                  "VarDecl backend-agnostico" che condivide il      ║
-- ║                  layer adapter Loquel e l'adapter HenQL.            ║
-- ║                                                                    ║
-- ║  La sostituzione `$name → valore` avviene lato Grafana; Penelope   ║
-- ║  emette solo il sentinella `$name` via `varRef`.                   ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Data.Bool          using (Bool; true; false; _∧_; not)
open import Data.List          using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.String        using (String; _++_)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
open import Relation.Nullary.Decidable.Core using (does)

-- Su quale datasource gira una query variable: due casi, espliciti.
--   • dsDefault  → il datasource Prometheus di default di Grafana;
--   • dsVar n    → segue la variabile-datasource di nome `n` (il picker).
-- Niente `Maybe String`: l'assenza di scelta È un caso con un nome.
data DSRef : Set where
  dsDefault : DSRef
  dsVar     : (varName : String) → DSRef

data VarSpec : Set where
  customSpec : List⁺ String → (multi includeAll : Bool) → VarSpec
  querySpec  : (sourceGrafanaType fld : String)
             → (multi includeAll : Bool) → VarSpec
  -- Variabile query Prometheus: `label_values(metric, lbl)` (o
  -- `label_values(lbl)` se il contesto metrica è `nothing`). La forma
  -- terms di `querySpec` è ES/Loki; Prometheus richiede questa.
  -- `ds` dice su quale datasource valutarla (default, o segui il picker).
  promQuerySpec : (metric : Maybe String) (lbl : String)
                → (multi includeAll : Bool) (ds : DSRef) → VarSpec
  -- Variabile di tipo "datasource": Grafana mostra un PICKER dei
  -- datasource del plugin indicato (es. "prometheus"). Il suo valore è
  -- l'uid del datasource scelto, referenziabile come `${name}`.
  datasourceSpec : (pluginId : String) → VarSpec

record Variable : Set where
  constructor mkVariable′
  field
    name : String
    spec : VarSpec

-- ── Smart constructor compat: la forma "custom" mantiene il vecchio
-- ── signature `mkVariable name options` (single-select, niente All).
mkVariable : String → List⁺ String → Variable
mkVariable n opts = record { name = n ; spec = customSpec opts false false }

-- ── Custom variable con multi/includeAll espliciti: lista statica di
-- ── valori (es. ambienti dev/qa/cu) selezionabili uno alla volta, in
-- ── gruppo (multi) o tutti insieme ("All").
mkCustomVariable : (name : String) → List⁺ String
                 → (multi includeAll : Bool) → Variable
mkCustomVariable n opts m a = record { name = n ; spec = customSpec opts m a }

-- ── Query variable: terms su `fld` del datasource `sourceGrafanaType`,
-- ── più i flag multi/includeAll. È il "VarDecl" backend-agnostico.
mkQueryVariable : (name sourceGrafanaType fld : String)
                  (multi includeAll : Bool) → Variable
mkQueryVariable n src f m a =
  record { name = n ; spec = querySpec src f m a }

-- ── Query variable Prometheus: `label_values([metric,] lbl)`. Il
-- ── `metric` opzionale restringe i valori alle serie esistenti.
mkPromVariable : (name : String) (metric : Maybe String) (lbl : String)
                 (multi includeAll : Bool) → Variable
mkPromVariable n m l mu a =
  record { name = n ; spec = promQuerySpec m l mu a dsDefault }

-- ── Come mkPromVariable, ma valutata sul datasource scelto via picker:
-- ── `dsVarName` è il NOME della variabile-datasource da seguire. Così il
-- ── picker pilota anche le variabili, non solo i pannelli.
mkPromVariableOn : (name dsVarName : String) (metric : Maybe String)
                   (lbl : String) (multi includeAll : Bool) → Variable
mkPromVariableOn n dv m l mu a =
  record { name = n ; spec = promQuerySpec m l mu a (dsVar dv) }

-- ── Variabile datasource: Grafana mostra un picker dei datasource del
-- ── plugin `pluginId` (es. "prometheus"); il valore è l'uid scelto.
mkDatasourceVariable : (name pluginId : String) → Variable
mkDatasourceVariable n p = record { name = n ; spec = datasourceSpec p }

-- ── Riferimento `$name` per sostituzione testuale (PromQL, titoli, …).
varRef : Variable → String
varRef v = "$" ++ Variable.name v

-- ── Well-formedness: due `Variable` con lo stesso `name` devono avere
-- ── la stessa `spec`. Implementato come Bool: uguaglianza definizionale
-- ── di sourceGrafanaType/fld/multi/includeAll (rispettivamente di
-- ── customSpec ↔ customSpec con lista uguale per le opzioni — qui mi
-- ── limito al caso `name` collision; la divergenza di forma o di
-- ── specifica produce `false`).

private
  _==ᵇ_ : Bool → Bool → Bool
  true  ==ᵇ true  = true
  false ==ᵇ false = true
  _     ==ᵇ _     = false

  sameMaybeˢ : Maybe String → Maybe String → Bool
  sameMaybeˢ nothing   nothing   = true
  sameMaybeˢ (just a)  (just b)  = does (a ≟ˢ b)
  sameMaybeˢ _         _         = false

  sameDSRef : DSRef → DSRef → Bool
  sameDSRef dsDefault   dsDefault   = true
  sameDSRef (dsVar a)   (dsVar b)   = does (a ≟ˢ b)
  sameDSRef _           _           = false

  sameSpec : VarSpec → VarSpec → Bool
  sameSpec (customSpec _ m₁ a₁) (customSpec _ m₂ a₂) =
    (m₁ ==ᵇ m₂) ∧ (a₁ ==ᵇ a₂)   -- opzioni: collisione tollerata; i flag no
  sameSpec (querySpec s₁ f₁ m₁ a₁) (querySpec s₂ f₂ m₂ a₂) =
    does (s₁ ≟ˢ s₂) ∧ does (f₁ ≟ˢ f₂) ∧ (m₁ ==ᵇ m₂) ∧ (a₁ ==ᵇ a₂)
  sameSpec (promQuerySpec m₁ l₁ mu₁ a₁ d₁) (promQuerySpec m₂ l₂ mu₂ a₂ d₂) =
    sameMaybeˢ m₁ m₂ ∧ does (l₁ ≟ˢ l₂) ∧ (mu₁ ==ᵇ mu₂) ∧ (a₁ ==ᵇ a₂)
      ∧ sameDSRef d₁ d₂
  sameSpec (datasourceSpec p₁) (datasourceSpec p₂) = does (p₁ ≟ˢ p₂)
  sameSpec _ _ = false

  -- v è compatibile con vs := per ogni w in vs con lo stesso `name`,
  -- spec(v) == spec(w).
  compatibleAll : Variable → List Variable → Bool
  compatibleAll _ []       = true
  compatibleAll v (w ∷ ws) with does (Variable.name v ≟ˢ Variable.name w)
  ... | true  = sameSpec (Variable.spec v) (Variable.spec w) ∧ compatibleAll v ws
  ... | false = compatibleAll v ws

varsConsistentB : List Variable → Bool
varsConsistentB []       = true
varsConsistentB (v ∷ vs) = compatibleAll v vs ∧ varsConsistentB vs
