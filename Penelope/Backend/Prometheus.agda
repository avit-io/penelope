{-# OPTIONS --safe --without-K #-}

module Penelope.Backend.Prometheus where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  HenQL/Prometheus backend per Penelope.                            ║
-- ║                                                                    ║
-- ║  HenQL : QueryLang istanziato a (Ctx=Model, QueryType=PromType,    ║
-- ║  Query=Expr). prometheus M : Datasource produce un datasource che  ║
-- ║  rende via prettyExpr e considera fedele OGNI Expr (HenQL È il     ║
-- ║  linguaggio nativo di Prometheus per il frammento che modelliamo). ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Prometea.Core           using (Model; PromType; Scalar; InstantVector)
open import HenQL.Syntax            using (Expr)
open import HenQL.Print             using (prettyExpr)

open import Penelope.Panel
open import Penelope.Query
open import Penelope.Datasource

open import Data.Bool   using (Bool; true)
open import Data.String using (String)

-- Il PromType che ogni kind esige.
henqlQueryTypeOf : PanelKind → PromType
henqlQueryTypeOf TimeSeries = InstantVector
henqlQueryTypeOf Stat       = Scalar
henqlQueryTypeOf Gauge      = Scalar
henqlQueryTypeOf BarGauge   = Scalar
henqlQueryTypeOf Table      = InstantVector

HenQL : QueryLang
HenQL = record
  { Ctx         = Model
  ; QueryType   = PromType
  ; Query       = Expr
  ; queryTypeOf = henqlQueryTypeOf
  }

prometheus : Model → Datasource
prometheus M = record
  { lang        = HenQL
  ; ctx         = M
  ; grafanaType = "prometheus"
  ; render      = λ e → prettyExpr e
  ; faithful?   = λ _ → true
  }
