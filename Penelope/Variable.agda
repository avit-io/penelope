{-# OPTIONS --safe --without-K #-}

module Penelope.Variable where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Template variables — placeholder che Grafana sostituisce a        ║
-- ║  runtime per parametrizzare le query.                              ║
-- ║                                                                    ║
-- ║  Due forme:                                                        ║
-- ║   • customSpec : lista esplicita di valori ("custom").             ║
-- ║   • querySpec  : terms-query su un campo + flag multi/includeAll   ║
-- ║                  ("query"). È la forma emessa dai riferimenti      ║
-- ║                  tipati `Var s` dell'adapter Loquel.               ║
-- ║                                                                    ║
-- ║  La sostituzione `$name → valore` avviene lato Grafana; Penelope   ║
-- ║  emette solo il sentinella `$name` via `varRef`.                   ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Data.Bool          using (Bool)
open import Data.List.NonEmpty using (List⁺)
open import Data.String        using (String; _++_)

data VarSpec : Set where
  customSpec : List⁺ String → VarSpec
  querySpec  : (fld : String) (multi includeAll : Bool) → VarSpec

record Variable : Set where
  constructor mkVariable′
  field
    name : String
    spec : VarSpec

-- ── Smart constructor compat: la forma "custom" mantiene il vecchio
-- ── signature `mkVariable name options`.
mkVariable : String → List⁺ String → Variable
mkVariable n opts = record { name = n ; spec = customSpec opts }

-- ── Query variable: terms su `fld`, multi/includeAll.
mkQueryVariable : (name fld : String) (multi includeAll : Bool) → Variable
mkQueryVariable n f m a = record { name = n ; spec = querySpec f m a }

-- ── Riferimento `$name` per sostituzione testuale (PromQL, titoli, …).
varRef : Variable → String
varRef v = "$" ++ Variable.name v
