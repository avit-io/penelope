module Examples.Tela where

open import Prometea.Core
open import HenQL.Syntax
open import Penelope.Panel
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

-- ── Template variable: $service ──
serviceVar : Variable
serviceVar = mkVariable "service" ("frontend" ∷ "backend" ∷ "api" ∷ [])

-- ── Tre panel con target tipate ──
errori : Panel miaApp TimeSeries
errori = timeseries "Errori / s"
  (sumBy ("job" ∷ [])
    (rate (range
      ("http_requests_errors_total{service=\"" ++ varRef serviceVar ++ "\"}")
      5)))

latenza : Panel miaApp TimeSeries
latenza = timeseries "Latenza"
  (rate (range
    ("http_request_duration_seconds_sum{service=\"" ++ varRef serviceVar ++ "\"}")
    5))

budget : Panel miaApp Stat
budget = stat "Budget consumato" (scalar "0.42")

-- ── Geometria con payload: tile carica direttamente l'AnyPanel ──
-- (left ↔ right) ↕ bot. left/right sono 12×8, bot è 24×8 → viewport 24×16.

viewport : Rect
viewport = mkRect 0 0 24 16

tela : TilingOf (AnyPanel miaApp) viewport
tela = (left ↔ right) ↕ bot
  where
    left  : Tiling (AnyPanel miaApp) 0 0 12 8
    left  = tile (□ errori)
    right : Tiling (AnyPanel miaApp) 12 0 12 8
    right = tile (□ latenza)
    bot   : Tiling (AnyPanel miaApp) 0 8 24 8
    bot   = tile (□ budget)

salute : Dashboard miaApp
salute = mkDashboard "Salute API" "salute-api"
                     (serviceVar ∷ [])
                     viewport tela

-- Il JSON Grafana corrispondente.
json : String
json = renderDashboard salute

-- ── Quello che il typechecker rifiuta strutturalmente ───────────────────
--
-- mismatch : Panel miaApp TimeSeries
-- mismatch = timeseries "Sbagliato" (scalar "1.0")
-- ✗ Expected: Expr miaApp InstantVector
-- ✗ Got:      Expr miaApp Scalar
