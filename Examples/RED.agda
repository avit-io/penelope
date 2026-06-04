module Examples.RED where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  RED dashboard — Rate, Errors, Duration su una lista di servizi.   ║
-- ║                                                                    ║
-- ║  Una riga per servizio, tre colonne (rate, err, dur). Il widget    ║
-- ║  per-servizio è `cols`-3 di celle 8×4; il widget dashboard è       ║
-- ║  `rows`-N di righe 24×4. Math: cols 3 → stackW 2 7 = 24; rows N →  ║
-- ║  stackH (N-1) 3. Con N = 4 servizi: stackH 3 3 = 16.               ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Prometea.Core
open import HenQL.Syntax
open import Penelope.Panel
open import Penelope.Tiling
open import Penelope.Dashboard
open import Penelope.JSON
open import Penelope.Sugar

open import Data.Nat    using (ℕ)
open import Data.Float  using (Float)
open import Data.String using (String; _++_)
open import Data.List   using (_∷_; [])
open import Data.Vec    using (Vec; _∷_; []; map)

-- ── Modello concreto ──────────────────────────────────────────────────
svc : Model
svc = record { Time = ℕ ; Val = Float ; Series = String }

-- ── Celle RED per servizio (ognuna è Widget 8×4) ──────────────────────

rateCell : String → Widget (AnyPanel svc) 8 4
rateCell n = tile (□ (timeseries (n ++ " · rate")
  (sumBy ("job" ∷ [])
    (rate (range ("http_requests_total{job=\"" ++ n ++ "\"}") 5)))))

errCell : String → Widget (AnyPanel svc) 8 4
errCell n = tile (□ (timeseries (n ++ " · errors")
  (sumBy ("job" ∷ [])
    (rate (range ("http_requests_total{job=\"" ++ n ++ "\",code=~\"5..\"}") 5)))))

durCell : String → Widget (AnyPanel svc) 8 4
durCell n = tile (□ (timeseries (n ++ " · p99")
  (histogramQuantile "0.99"
    (sumBy ("le" ∷ [])
      (rate (range
        ("http_request_duration_seconds_bucket{job=\"" ++ n ++ "\"}")
        5))))))

-- ── Una riga RED: cols su 3 celle 8×4 → 24×4 ──────────────────────────
redRow : String → Widget (AnyPanel svc) 24 4
redRow n = cols (rateCell n ∷ errCell n ∷ durCell n ∷ [])

-- ── I servizi monitorati ──────────────────────────────────────────────
servizi : Vec String 4
servizi = "checkout" ∷ "catalog" ∷ "payments" ∷ "search" ∷ []

-- ── La tela: rows su 4 righe 24×4 → 24×16 ─────────────────────────────
tela : Widget (AnyPanel svc) 24 16
tela = rows (map redRow servizi)

-- ── La dashboard ──────────────────────────────────────────────────────
viewport : Rect
viewport = mkRect 0 0 24 16

red : Dashboard svc
red = mkDashboard "RED — Servizi" "red-servizi" [] viewport (tela {0} {0})

-- Il JSON Grafana corrispondente.
json : String
json = renderDashboard red
