{-# OPTIONS --safe --without-K #-}

module Penelope.Backend.Prometheus where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  HenQL/Prometheus backend per Penelope.                            ║
-- ║                                                                    ║
-- ║  HenQL : QueryLang istanziato a (Ctx=Model, QueryType=PromType,    ║
-- ║  Query=Expr). prometheus M : Datasource produce un datasource che  ║
-- ║  rende via prettyExpr e considera fedele OGNI Expr (HenQL È il     ║
-- ║  linguaggio nativo di Prometheus per il frammento che modelliamo). ║
-- ║                                                                    ║
-- ║  Riferimento a variabile in posizione di label-matcher:            ║
-- ║                                                                    ║
-- ║    _=ᵛ_ : (label : String) → Variable → Matcher M                  ║
-- ║                                                                    ║
-- ║  Semantica fedele a PromQL:                                        ║
-- ║   · multi=false → `label="$name"`   (uguaglianza esatta).          ║
-- ║   · multi=true  → `label=~"$name"`  (Grafana interpola come        ║
-- ║                    alternanza regex `v₁|v₂` → disgiunzione di      ║
-- ║                    uguaglianze esatte: FEDELE).                    ║
-- ║                                                                    ║
-- ║  `includeAll` non è espresso nel matcher: chi lo vuole usa "All"   ║
-- ║  lato Grafana e il templating substituisce `.*` (`allValue=".*"`)  ║
-- ║  oppure il caller omette il matcher. Onestà: le label PromQL sono  ║
-- ║  APERTE, qui non c'è la garanzia "il campo esiste" che vale per    ║
-- ║  Loquel; il matcher è solo ben formato su un nome.                 ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Prometea.Core           using (Model; PromType; Scalar; InstantVector)
open import HenQL.Syntax            using (Expr; Matcher; mkMatcher; MatchOp;
                                            meq; mregex)
open import HenQL.Print             using (prettyExpr)

open import Penelope.Panel
open import Penelope.Query
open import Penelope.Datasource
open import Penelope.Variable       using (Variable; VarSpec; querySpec;
                                            promQuerySpec; customSpec)

open import Data.Bool   using (Bool; true; false)
open import Data.Maybe  using (nothing)
open import Data.String using (String; _++_)

-- Il PromType che ogni kind esige.
henqlQueryTypeOf : PanelKind → PromType
henqlQueryTypeOf TimeSeries    = InstantVector
henqlQueryTypeOf Stat          = Scalar
henqlQueryTypeOf Gauge         = Scalar
henqlQueryTypeOf BarGauge      = Scalar
henqlQueryTypeOf Table         = InstantVector
henqlQueryTypeOf StatusHistory = InstantVector

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
  ; uid         = nothing
  ; render      = λ e → prettyExpr e
  ; faithful?   = λ _ → true
  }

-- ── Matcher su variabile di dashboard ───────────────────────────────
--
-- Sceglie `=` o `=~` in base al flag `multi` della Variable, uniforme
-- su query/promQuery/custom: con multi Grafana interpola l'alternanza
-- regex `v₁|v₂`, che con `=~` resta una disgiunzione di uguaglianze.
private
  varMatchOp : Variable → MatchOp
  varMatchOp v with Variable.spec v
  ... | querySpec _ _ true  _      = mregex
  ... | querySpec _ _ false _      = meq
  ... | promQuerySpec _ _ true  _  = mregex
  ... | promQuerySpec _ _ false _  = meq
  ... | customSpec _ true  _       = mregex
  ... | customSpec _ false _       = meq

infix 4 _=ᵛ_
_=ᵛ_ : ∀ {M} → (label : String) → (v : Variable) → Matcher M
lbl =ᵛ v = mkMatcher lbl (varMatchOp v) ("$" ++ Variable.name v)
