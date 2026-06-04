module Penelope.Dashboard where

open import Prometea.Core
open import Penelope.Layout
open import Data.String using (String)

-- Una dashboard è un titolo + un identificatore + una tela tessuta.
-- M è fissato dal record: tutti i panel del Layout condividono lo stesso
-- modello semantico — phantom da Layout M, propagato dal typechecker.
record Dashboard (M : Model) : Set where
  constructor mkDashboard
  field
    title  : String
    uid    : String
    canvas : Layout M
