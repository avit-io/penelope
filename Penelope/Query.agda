{-# OPTIONS --safe --without-K #-}

module Penelope.Query where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  QueryLang — astrazione neutra del linguaggio di query del         ║
-- ║  backend. Penelope dipende solo da:                                ║
-- ║   • un tipo Ctx (Set₁) di "contesto" su cui la query è indicizzata ║
-- ║     (Model per HenQL, Schema lifted per Loquel);                   ║
-- ║   • un tipo QueryType dei "kind" di query;                         ║
-- ║   • la famiglia Query : Ctx → QueryType → Set delle query tipate;  ║
-- ║   • la mappa queryTypeOf che dice, per ogni PanelKind, quale       ║
-- ║     QueryType la sua target deve avere.                            ║
-- ║                                                                    ║
-- ║  Ctx è in Set₁ per accomodare HenQL (`Model : Set₁`). Loquel       ║
-- ║  usa una `Lift _ Schema`.                                          ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Penelope.Panel using (PanelKind)

record QueryLang : Set₂ where
  field
    Ctx         : Set₁
    QueryType   : Set
    Query       : Ctx → QueryType → Set
    queryTypeOf : PanelKind → QueryType
