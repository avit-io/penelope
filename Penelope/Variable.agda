module Penelope.Variable where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Template variables — placeholder che il consumer Grafana sceglie ║
-- ║  a runtime per parametrizzare le query di tutta la dashboard.      ║
-- ║                                                                    ║
-- ║  Tipologia MVP: "custom" — lista esplicita di valori. Le altre     ║
-- ║  tipologie Grafana (query / interval / constant / text /           ║
-- ║  datasource) vivono in roadmap.                                    ║
-- ║                                                                    ║
-- ║  La sostituzione `$varname → valore` avviene a livello Grafana     ║
-- ║  prima dell'invio a Prometheus. Penelope emette il nome `$varname` ║
-- ║  nella stringa PromQL via `varRef`; non fa sostituzione lato Agda. ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Data.List.NonEmpty using (List⁺)
open import Data.String        using (String; _++_)

record Variable : Set where
  constructor mkVariable
  field
    name    : String
    options : List⁺ String

-- Riferimento alla variabile in una stringa PromQL: `$varname`.
-- Grafana sostituisce con il valore corrente al render del panel.
varRef : Variable → String
varRef v = "$" ++ Variable.name v
