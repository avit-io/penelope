module Examples.Tela where

open import Prometea.Core
open import HenQL.Syntax
open import Penelope.Panel
open import Penelope.Tiling
open import Penelope.Dashboard
open import Penelope.JSON

open import Data.Nat     using (ℕ)
open import Data.Float   using (Float)
open import Data.String  using (String)
open import Data.List    using (_∷_; [])
open import Data.Product using (_,_)

-- Un modello concreto: timestamp interi, valori float, serie come stringhe.
miaApp : Model
miaApp = record { Time = ℕ ; Val = Float ; Series = String }

-- ── Tre panel, tre kind, tre target tipate ──────────────────────────────

errori : Panel miaApp TimeSeries
errori = mkPanel "Errori / s"
  (sumBy ("job" ∷ []) (rate (range "http_requests_errors_total" 5)))

latenza : Panel miaApp TimeSeries
latenza = mkPanel "Latenza"
  (rate (range "http_request_duration_seconds_sum" 5))

budget : Panel miaApp Stat
budget = mkPanel "Budget consumato" (scalar "0.42")

-- ── Geometria: tassellamento del viewport ──────────────────────────────
-- Viewport 24×16. Tassellamento: hcut(8/8), top-half è vcut(12/12).
-- Le sotto-tile sono annotate col tipo per permettere ad Agda di
-- inferire ht/hb e wl/wr dei cut.

viewport : Rect
viewport = mkRect 0 0 24 16

tela : TilingOf viewport
tela = hcut top bot
  where
    top : Tiling 0 0 24 8
    top = vcut left right
      where
        left  : Tiling 0 0 12 8
        left  = tile
        right : Tiling 12 0 12 8
        right = tile
    bot : Tiling 0 8 24 8
    bot = tile

-- ── Decorazione: etichetta ogni foglia con un panel ────────────────────
-- Per costruzione (lemmi disjoint + contained), i tre panel sono in
-- regioni disgiunte del viewport e nessuno esce dal canvas.

decora : Leaf tela → AnyPanel miaApp
decora (topL (leftL here))  = TimeSeries , errori
decora (topL (rightL here)) = TimeSeries , latenza
decora (botL here)          = Stat , budget

salute : Dashboard miaApp
salute = mkDashboard "Salute API" "salute-api" viewport tela decora

-- Il JSON Grafana corrispondente. Totale, sintatticamente valido,
-- con gridPos disgiunti e contenuti nel viewport per costruzione.
json : String
json = renderDashboard salute

-- ── Quello che il typechecker rifiuta strutturalmente ───────────────────
--
-- mismatch : Panel miaApp TimeSeries
-- mismatch = mkPanel "Sbagliato" (scalar "1.0")
-- ✗ Expected: Expr miaApp InstantVector
-- ✗ Got:      Expr miaApp Scalar
--
-- La regola "TimeSeries vuole un vettore" non è in un commento:
-- è nel tipo di `target`, derivato da `queryTypeOf k`.
