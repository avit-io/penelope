module Penelope.Panel where

open import Prometea.Core
open import HenQL.Syntax
open import Data.String using (String)

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
-- Il tipo di `target` non è scelto: è imposto dal kind, e Agda lo verifica
-- nel sito di costruzione. Nessuna prova attaccata: il tipo È la prova.
record Panel (M : Model) (k : PanelKind) : Set where
  constructor mkPanel
  field
    title  : String
    target : Expr M (queryTypeOf k)
