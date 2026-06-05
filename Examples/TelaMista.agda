{-# OPTIONS --safe --without-K #-}

module Examples.TelaMista where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Tela mista — un panel Prometheus accanto a un panel Loki, nella   ║
-- ║  stessa dashboard. Prova che il datasource è PER-PANEL: il JSON     ║
-- ║  emesso porta due campi `datasource.type` distinti e due formati   ║
-- ║  di query distinti (PromQL via prettyExpr, LogQL via renderLogQL). ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Prometea.Core
open import HenQL.Syntax
open import Loquel.Schema       using (Schema; TStr)
open import Loquel.Expr         using (var; lit; _≡ᵉ_)
open import Loquel.Pipe         using (Pipe; filterp)

open import Data.List.Membership.Propositional        using (_∈_)
open import Data.List.Relation.Unary.Any              using (here; there)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Data.Unit                                  using (tt)

open import Penelope.Panel
open import Penelope.Datasource
open import Penelope.Backend.Prometheus
open import Penelope.Backend.Loquel
open import Penelope.Tiling
open import Penelope.Dashboard
open import Penelope.JSON
open import Penelope.Sugar

open import Data.Nat    using (ℕ)
open import Data.Float  using (Float)
open import Data.String using (String)
open import Data.List    using (_∷_; [])
open import Data.Product using (_,_)

-- ── Datasource Prometheus ─────────────────────────────────────────────
miaApp : Model
miaApp = record { Time = ℕ ; Val = Float ; Series = String }

promApp : Datasource
promApp = prometheus miaApp

-- ── Schema Loki + datasource Loki ─────────────────────────────────────
logSchema : Schema
logSchema = ("app" , TStr) ∷ ("line" , TStr) ∷ []

app∈ : ("app" , TStr) ∈ logSchema
app∈ = here refl

lokiApp : Datasource
lokiApp = loki logSchema

-- ── Panel Prometheus: Stat con uno scalar HenQL ───────────────────────
budget : Panel promApp Stat
budget = stat "Budget consumato" (scalar "0.42")

-- ── Panel Loki: Table con uno stream selector (frammento fedele) ──────
streamP : Pipe logSchema logSchema
streamP = filterp (var app∈ ≡ᵉ lit "webapp")

lokiTable : Panel lokiApp Table
lokiTable = mkPanel1 "Webapp logs" (logT streamP)

-- ── La tela: 12×8 budget ↔ 12×8 lokiTable → viewport 24×8 ────────────
viewport : Rect
viewport = mkRect 0 0 24 8

tela : TilingOf AnyPanel viewport
tela = left ↔ right
  where
    left  : Tiling AnyPanel 0 0 12 8
    left  = tile (□ budget)
    right : Tiling AnyPanel 12 0 12 8
    right = tile (□ lokiTable)

mista : Dashboard
mista = mkDashboard "Mista — Prometheus & Loki" "mista" [] viewport tela

-- Il JSON Grafana corrispondente: due datasource distinti, due formati
-- di query distinti, nella stessa dashboard.
json : String
json = renderDashboard mista
