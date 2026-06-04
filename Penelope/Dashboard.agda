module Penelope.Dashboard where

open import Prometea.Core
open import Penelope.Panel
open import Penelope.Tiling
open import Data.String using (String)

-- Una dashboard è la decorazione di un tassellamento con panel: geometria
-- (Tiling) + payload (label che etichetta ogni foglia con un AnyPanel).
--
-- Separazione netta: la geometria sta in Penelope.Tiling (slicing floor-
-- plan), Grafana sta nei panel. Dashboard è solo il container.
--
-- Per costruzione (lemmi disjoint + contained in Tiling):
--   • tutti i panel occupano regioni DISGIUNTE del viewport;
--   • nessun panel esce dal viewport;
--   • ogni cella ha w ≥ 1 e h ≥ 1 (suc-indexed nei figli di hcut/vcut).
--
-- Tutti i panel condividono lo stesso modello M (phantom da AnyPanel M).
record Dashboard (M : Model) : Set where
  constructor mkDashboard
  field
    title    : String
    uid      : String
    viewport : Rect
    tiling   : TilingOf viewport
    label    : Leaf tiling → AnyPanel M
