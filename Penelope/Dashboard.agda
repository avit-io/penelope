module Penelope.Dashboard where

open import Prometea.Core
open import Penelope.Panel
open import Penelope.Tiling
open import Penelope.Variable
open import Data.List   using (List)
open import Data.String using (String)

-- Una dashboard è la decorazione di un tassellamento con panel: geometria
-- (Tiling) + payload (panel nei tile) + eventuali template variables.
--
-- Tiling è content-polimorfo (`Tiling C x y w h`); qui si istanzia
-- `C := AnyPanel M`. Tutti i panel della dashboard condividono lo stesso
-- modello M (coerenza del modello: phantom da AnyPanel M).
--
-- Per costruzione (lemmi disjoint + contained in Tiling, universali su C):
--   • tutti i panel occupano regioni DISGIUNTE del viewport;
--   • nessun panel esce dal viewport;
--   • ogni cella ha w ≥ 1 e h ≥ 1 (suc-indexed nei figli di hcut/vcut).
record Dashboard (M : Model) : Set where
  constructor mkDashboard
  field
    title     : String
    uid       : String
    variables : List Variable
    viewport  : Rect
    tiling    : TilingOf (AnyPanel M) viewport
