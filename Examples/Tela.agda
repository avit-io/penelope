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

-- Un modello concreto: timestamp interi, valori float, serie come stringhe.
miaApp : Model
miaApp = record { Time = ℕ ; Val = Float ; Series = String }

-- ── Una template variable: `$service`, scelta fra tre valori. ──────────
-- Grafana sostituisce `$service` con il valore scelto a runtime prima
-- dell'invio della query a Prometheus.

serviceVar : Variable
serviceVar = mkVariable "service"
  ("frontend" ∷ "backend" ∷ "api" ∷ [])

-- ── Tre panel, tre kind, target che usano la variabile via `varRef`. ──

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

-- ── Geometria: tassellamento 24×16, con infix ↕/↔. ─────────────────────

viewport : Rect
viewport = mkRect 0 0 24 16

tela : TilingOf viewport
tela = (left ↔ right) ↕ bot
  where
    left  : Tiling 0 0 12 8
    left  = tile
    right : Tiling 12 0 12 8
    right = tile
    bot   : Tiling 0 8 24 8
    bot   = tile

-- ── Decorazione: ogni foglia → un panel, kind recuperato da □_. ────────

decora : Leaf tela → AnyPanel miaApp
decora (topL (leftL here))  = □ errori
decora (topL (rightL here)) = □ latenza
decora (botL here)          = □ budget

-- ── Dashboard con `serviceVar` registrata fra le variabili. ────────────

salute : Dashboard miaApp
salute = mkDashboard "Salute API" "salute-api"
                     (serviceVar ∷ [])
                     viewport tela decora

-- Il JSON Grafana corrispondente, con il blocco `templating.list`
-- emesso da renderTemplating in JSON.agda.
json : String
json = renderDashboard salute

-- ── Quello che il typechecker rifiuta strutturalmente ───────────────────
--
-- mismatch : Panel miaApp TimeSeries
-- mismatch = timeseries "Sbagliato" (scalar "1.0")
-- ✗ Expected: Expr miaApp InstantVector
-- ✗ Got:      Expr miaApp Scalar
