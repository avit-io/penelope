module Examples.Tela where

open import Prometea.Core
open import HenQL.Syntax
open import Penelope.Panel
open import Penelope.Layout
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

-- TimeSeries → la target DEVE essere Expr miaApp InstantVector.
errori : Panel miaApp TimeSeries
errori = mkPanel "Errori / s"
  (sumBy ("job" ∷ []) (rate (range "http_requests_errors_total" 5)))

latenza : Panel miaApp TimeSeries
latenza = mkPanel "Latenza"
  (rate (range "http_request_duration_seconds_sum" 5))

-- Stat → la target DEVE essere Expr miaApp Scalar.
budget : Panel miaApp Stat
budget = mkPanel "Budget consumato" (scalar "0.42")

-- ── La tela: due grafici accanto in alto, un valore singolo in basso ────
-- Per costruzione (BSP) le tre celle non si sovrappongono.
tela : Layout miaApp
tela = above (beside (cell (TimeSeries , errori))
                     (cell (TimeSeries , latenza)))
             (cell (Stat , budget))

salute : Dashboard miaApp
salute = mkDashboard "Salute API" "salute-api" tela

-- Il JSON Grafana corrispondente. Totale, sintatticamente valido.
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
