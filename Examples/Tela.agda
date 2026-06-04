module Examples.Tela where

open import Prometea.Core
open import HenQL.Syntax
open import Penelope.Panel
open import Penelope.Tiling
open import Penelope.Dashboard
open import Penelope.JSON
open import Penelope.Sugar

open import Data.Nat     using (ℕ)
open import Data.Float   using (Float)
open import Data.String  using (String)
open import Data.List    using (_∷_; [])

-- Un modello concreto: timestamp interi, valori float, serie come stringhe.
miaApp : Model
miaApp = record { Time = ℕ ; Val = Float ; Series = String }

-- ── Tre panel, tre kind, tre target tipate (con sugar per-kind) ─────────
-- timeseries/stat sono mkPanel + singleton List⁺: il kind è nel nome
-- della funzione, il tipo della target è imposto da queryTypeOf.

errori : Panel miaApp TimeSeries
errori = timeseries "Errori / s"
  (sumBy ("job" ∷ []) (rate (range "http_requests_errors_total" 5)))

latenza : Panel miaApp TimeSeries
latenza = timeseries "Latenza"
  (rate (range "http_request_duration_seconds_sum" 5))

budget : Panel miaApp Stat
budget = stat "Budget consumato" (scalar "0.42")

-- ── Geometria: tassellamento del viewport con infix ↕/↔ ────────────────
-- ↕ è hcut (top sopra bot), ↔ è vcut (left accanto a right). Le
-- sotto-tile sono annotate col tipo per permettere ad Agda di inferire
-- ht/hb e wl/wr dei cut — i ℕ-indici di Tiling non si invertono da
-- `suc n + suc n ≡ 16` senza aiuto.

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

-- ── Decorazione: ogni foglia → un panel, via □_ ────────────────────────
-- □ errori sostituisce (TimeSeries , errori) — il kind è già nel tipo
-- di errori, ed è ridondante ripeterlo nel pairing Σ.

decora : Leaf tela → AnyPanel miaApp
decora (topL (leftL here))  = □ errori
decora (topL (rightL here)) = □ latenza
decora (botL here)          = □ budget

salute : Dashboard miaApp
salute = mkDashboard "Salute API" "salute-api" viewport tela decora

-- Il JSON Grafana corrispondente.
json : String
json = renderDashboard salute

-- ── Quello che il typechecker rifiuta strutturalmente ───────────────────
--
-- mismatch : Panel miaApp TimeSeries
-- mismatch = timeseries "Sbagliato" (scalar "1.0")
-- ✗ Expected: Expr miaApp InstantVector
-- ✗ Got:      Expr miaApp Scalar
--
-- La regola "timeseries vuole un InstantVector" è nella firma della
-- funzione, derivata da queryTypeOf TimeSeries. Errore di unificazione
-- sul sito di chiamata, non commento nella documentazione.
