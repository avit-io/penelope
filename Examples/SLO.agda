module Examples.SLO where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  SLO dashboard — un widget per servizio con quattro panel:         ║
-- ║   • gauge      "SLI"         — rapporto 30g ok/totale              ║
-- ║   • bargauge   "Budget"      — 1 - (1-SLI)/(1-SLO)                 ║
-- ║   • stat       "Burn rate"   — (1-SLI_1h)/(1-SLO)                  ║
-- ║   • timeseries "SLI 30g"     — andamento ratio sui 5m              ║
-- ║                                                                    ║
-- ║  Math: ogni cella in alto è 8×4 (cols 3 → 24×4), il trend è 24×8,  ║
-- ║  sopra/sotto via ↕ → widget 24×12. N=4 servizi → 24×48.            ║
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

-- ── SLO definition ────────────────────────────────────────────────────
record SLO : Set where
  constructor mkSLO
  field target : String   -- es. "0.999"

defaultSLO : SLO
defaultSLO = mkSLO "0.999"

-- ── Helpers per i selettori dei job ───────────────────────────────────
ok : String → String
ok n = "http_requests_total{job=\"" ++ n ++ "\",code!~\"5..\"}"

tot : String → String
tot n = "http_requests_total{job=\"" ++ n ++ "\"}"

-- ── SLI: rapporto 30 giorni ok/totale (43200 minuti = 30g) ────────────
sli : SLO → String → Expr svc Scalar
sli s n = toScalar
  (sumBy [] (rate (range (ok n) 43200)) ÷
   sumBy [] (rate (range (tot n) 43200)))

-- ── SLI trend: ratio sui 5 minuti ─────────────────────────────────────
sliTrend : String → Expr svc InstantVector
sliTrend n =
  sumBy [] (rate (range (ok n) 5)) ÷
  sumBy [] (rate (range (tot n) 5))

-- ── Budget rimanente: 1 - (1-SLI)/(1-SLO) ─────────────────────────────
budgetRemaining : SLO → String → Expr svc Scalar
budgetRemaining s n = toScalar
  (litVec "1" - ((litVec "1" - sliVec) ÷ (litVec "1" - litVec (SLO.target s))))
  where
    sliVec : Expr svc InstantVector
    sliVec =
      sumBy [] (rate (range (ok n) 43200)) ÷
      sumBy [] (rate (range (tot n) 43200))

-- ── Burn rate: (1 - SLI_1h)/(1 - SLO), 60 minuti ──────────────────────
burnRate : SLO → String → Expr svc Scalar
burnRate s n = toScalar
  ((litVec "1" - sli1h) ÷ (litVec "1" - litVec (SLO.target s)))
  where
    sli1h : Expr svc InstantVector
    sli1h =
      sumBy [] (rate (range (ok n) 60)) ÷
      sumBy [] (rate (range (tot n) 60))

-- ── Le quattro celle per servizio ─────────────────────────────────────

gaugeCell : SLO → String → Widget (AnyPanel svc) 8 4
gaugeCell s n = tile (□ (gauge (n ++ " · SLI") (sli s n)))

budgetCell : SLO → String → Widget (AnyPanel svc) 8 4
budgetCell s n = tile (□ (bargauge (n ++ " · Budget") (budgetRemaining s n)))

burnCell : SLO → String → Widget (AnyPanel svc) 8 4
burnCell s n = tile (□ (stat (n ++ " · Burn rate") (burnRate s n)))

trendCell : SLO → String → Widget (AnyPanel svc) 24 8
trendCell _ n = tile (□ (timeseries (n ++ " · SLI 30g") (sliTrend n)))

-- ── Widget per servizio: cols dei tre indicatori sopra il trend ───────
-- 24×4 ↕ 24×8 → 24×12
sloWidget : SLO → String → Widget (AnyPanel svc) 24 12
sloWidget s n =
  cols (gaugeCell s n ∷ budgetCell s n ∷ burnCell s n ∷ [])
  ↕ trendCell s n

-- ── I servizi monitorati ──────────────────────────────────────────────
servizi : Vec String 4
servizi = "checkout" ∷ "catalog" ∷ "payments" ∷ "search" ∷ []

-- ── La dashboard: rows su 4 widget 24×12 → 24×48 (= stackH 3 11) ──────
dash : Widget (AnyPanel svc) 24 48
dash = rows (map (sloWidget defaultSLO) servizi)

viewport : Rect
viewport = mkRect 0 0 24 48

slo : Dashboard svc
slo = mkDashboard "SLO — Servizi" "slo-servizi" [] viewport (dash {0} {0})

-- Il JSON Grafana corrispondente.
json : String
json = renderDashboard slo
