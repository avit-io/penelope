module Penelope.Layout where

open import Prometea.Core
open import Penelope.Panel
open import Data.Product using (Σ; _,_)

-- Un panel di kind qualunque sotto il modello M.
-- L'esistenziale nasconde il kind ma il modello resta fisso: tutti i panel
-- della stessa tela condividono lo stesso M.
AnyPanel : Model → Set
AnyPanel M = Σ PanelKind (Panel M)

-- La tela: un albero di partizioni binarie del rettangolo (BSP).
-- Ogni nodo divide una regione in due sotto-regioni disgiunte. Per
-- costruzione, due celle (foglie) non possono mai sovrapporsi — vivono
-- in rettangoli disgiunti di un partizionamento. Non c'è bisogno di una
-- prova .non-overlap: la struttura È la prova.
data Layout (M : Model) : Set where
  cell   : AnyPanel M                            → Layout M
  above  : (top  : Layout M) (bot   : Layout M) → Layout M
  beside : (lft  : Layout M) (rgt   : Layout M) → Layout M
