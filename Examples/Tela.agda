{-# OPTIONS --safe --without-K #-}

module Examples.Tela where

open import Prometea.Core
open import HenQL.Syntax
open import Penelope.Panel
open import Penelope.Datasource
open import Penelope.Backend.Prometheus
open import Penelope.Tiling
open import Penelope.Dashboard
open import Penelope.JSON
open import Penelope.Sugar

open import Data.Nat           using (ℕ)
open import Data.Float         using (Float)
open import Data.String        using (String; _++_)
open import Data.List          using (_∷_; [])
open import Data.List.NonEmpty using (_∷_)

-- Un modello concreto.
miaApp : Model
miaApp = record { Time = ℕ ; Val = Float ; Series = String }

-- Datasource Prometheus su questo modello (per-panel d'ora in poi).
promApp : Datasource
promApp = prometheus miaApp

-- ── Template variable: $service ──
serviceVar : Variable
serviceVar = mkVariable "service" ("frontend" ∷ "backend" ∷ "api" ∷ [])

-- ── Tre panel con target tipate, tutti sullo stesso datasource ──
errori : Panel promApp TimeSeries
errori = timeseries "Errori / s"
  (sumBy ("job" ∷ [])
    (rate (range
      ("http_requests_errors_total{service=\"" ++ varRef serviceVar ++ "\"}")
      5)))

latenza : Panel promApp TimeSeries
latenza = timeseries "Latenza"
  (rate (range
    ("http_request_duration_seconds_sum{service=\"" ++ varRef serviceVar ++ "\"}")
    5))

budget : Panel promApp Stat
budget = stat "Budget consumato" (scalar "0.42")

-- ── Geometria con payload: tile carica direttamente l'AnyPanel ──
-- (left ↔ right) ↕ bot. left/right sono 12×8, bot è 24×8 → viewport 24×16.

viewport : Rect
viewport = mkRect 0 0 24 16

tela : TilingOf AnyPanel viewport
tela = (left ↔ right) ↕ bot
  where
    left  : Tiling AnyPanel 0 0 12 8
    left  = tile (□ errori)
    right : Tiling AnyPanel 12 0 12 8
    right = tile (□ latenza)
    bot   : Tiling AnyPanel 0 8 24 8
    bot   = tile (□ budget)

salute : Dashboard
salute = mkDashboard "Salute API" "salute-api"
                     (serviceVar ∷ [])
                     viewport tela

-- Il JSON Grafana corrispondente.
json : String
json = renderDashboard salute

-- ── Quello che il typechecker rifiuta strutturalmente ───────────────────
--
-- mismatch : Panel promApp TimeSeries
-- mismatch = timeseries "Sbagliato" (scalar "1.0")
-- ✗ Expected: Expr miaApp InstantVector
-- ✗ Got:      Expr miaApp Scalar
