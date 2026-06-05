{-# OPTIONS --safe --without-K #-}

module Penelope.Variable where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Template variables — placeholder che Grafana sostituisce a        ║
-- ║  runtime per parametrizzare le query.                              ║
-- ║                                                                    ║
-- ║  Due forme:                                                        ║
-- ║   • customSpec : lista esplicita di valori ("custom").             ║
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
open import Data.String        using (String; _++_)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
open import Relation.Nullary.Decidable.Core using (does)

data VarSpec : Set where
  customSpec : List⁺ String → VarSpec
  querySpec  : (sourceGrafanaType fld : String)
             → (multi includeAll : Bool) → VarSpec

record Variable : Set where
  constructor mkVariable′
  field
    name : String
    spec : VarSpec

-- ── Smart constructor compat: la forma "custom" mantiene il vecchio
-- ── signature `mkVariable name options`.
mkVariable : String → List⁺ String → Variable
mkVariable n opts = record { name = n ; spec = customSpec opts }

-- ── Query variable: terms su `fld` del datasource `sourceGrafanaType`,
-- ── più i flag multi/includeAll. È il "VarDecl" backend-agnostico.
mkQueryVariable : (name sourceGrafanaType fld : String)
                  (multi includeAll : Bool) → Variable
mkQueryVariable n src f m a =
  record { name = n ; spec = querySpec src f m a }

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

  sameSpec : VarSpec → VarSpec → Bool
  sameSpec (customSpec _) (customSpec _) = true  -- custom collisione: tollerata
  sameSpec (querySpec s₁ f₁ m₁ a₁) (querySpec s₂ f₂ m₂ a₂) =
    does (s₁ ≟ˢ s₂) ∧ does (f₁ ≟ˢ f₂) ∧ (m₁ ==ᵇ m₂) ∧ (a₁ ==ᵇ a₂)
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
