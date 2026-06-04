module Penelope.Panel where

open import Prometea.Core
open import HenQL.Syntax
open import Data.Product       using (Σ)
open import Data.String        using (String)
open import Data.List.NonEmpty using (List⁺)

-- Le famiglie di panel Grafana che Penelope sa tessere.
-- Ogni kind determina strutturalmente il PromType ammesso per la target.
data PanelKind : Set where
  TimeSeries : PanelKind
  Stat       : PanelKind
  Gauge      : PanelKind
  Table      : PanelKind

-- Il PromType che ogni kind esige.
-- È una funzione, non un campo: il tipo è derivato, non scelto a parte.
queryTypeOf : PanelKind → PromType
queryTypeOf TimeSeries = InstantVector
queryTypeOf Stat       = Scalar
queryTypeOf Gauge      = Scalar
queryTypeOf Table      = InstantVector

-- Un panel sotto il modello M, di un certo kind k.
-- Il tipo delle `targets` non è scelto: è imposto dal kind, e Agda lo
-- verifica nel sito di costruzione. Nessuna prova attaccata: il tipo È
-- la prova. Grafana supporta più query per panel (overlay di metriche),
-- quindi `targets` è una lista non vuota di espressioni tutte dello
-- stesso PromType `queryTypeOf k`.
record Panel (M : Model) (k : PanelKind) : Set where
  constructor mkPanel
  field
    title   : String
    targets : List⁺ (Expr M (queryTypeOf k))

-- Un panel di kind qualunque sotto il modello M.
-- L'esistenziale nasconde il kind ma il modello resta fisso: tutti i panel
-- della stessa tela condividono lo stesso M.
AnyPanel : Model → Set
AnyPanel M = Σ PanelKind (Panel M)
