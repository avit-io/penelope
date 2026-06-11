{-# OPTIONS --safe --without-K #-}

module Penelope.Sugar where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Zucchero sintattico per la composizione di dashboard.             ║
-- ║                                                                    ║
-- ║  Tutto qui sono DEFINIZIONI: si riducono ai costruttori esistenti  ║
-- ║  (tile, hcut, vcut, mkPanel, …) e al pairing di AnyPanel. Nessun   ║
-- ║  nuovo data type, nessuna prova ulteriore: gli invarianti del      ║
-- ║  livello geometrico (disgiunzione, contenimento, min-size,         ║
-- ║  universali su C) e quelli della decorazione (coerenza             ║
-- ║  panel↔query↔datasource per-panel) si propagano gratuitamente.     ║
-- ║                                                                    ║
-- ║  ↕/↔ sono polimorfi in C ∈ Set ℓ: il datasource compare solo dove ║
-- ║  si posiziona un panel via tile (□ …).                             ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Prometea.Core
open import HenQL.Syntax
open import Penelope.Panel
open import Penelope.Query
open import Penelope.Datasource
open import Penelope.Backend.Prometheus
open import Penelope.Tiling
open import Penelope.Variable  public
open import Penelope.Dashboard

open import Level              using (Level)
open import Data.Bool          using (T)
open import Data.Unit          using (tt)
open import Data.Maybe         using (just)
open import Data.Nat           using (ℕ; zero; suc; _+_)
open import Data.Product       using (_,_)
open import Data.List          using (List; _∷_; _++_)
open import Data.List.NonEmpty using (List⁺; [_])
open import Data.Vec           using (Vec; _∷_; [])
open import Data.String        using (String)

-- ─────────────────────────────────────────────────────────────────────
-- □_: AnyPanel da Panel con datasource e kind impliciti.
-- ─────────────────────────────────────────────────────────────────────

□_ : ∀ {ds k} → Panel ds k → AnyPanel
□_ {ds = ds} {k = k} p = record { ds = ds ; kind = k ; panel = p }
infix 9 □_

-- ─────────────────────────────────────────────────────────────────────
-- Costruttori per-kind sul backend Prometheus.
-- Il datasource (`prometheus M`) è dedotto dal tipo della Expr; per
-- HenQL il frammento fedele è vacuo, quindi `ok = tt` (T true = ⊤).
-- ─────────────────────────────────────────────────────────────────────

timeseries : ∀ {M} → String → Expr M InstantVector → Panel (prometheus M) TimeSeries
timeseries t e = mkPanel1 t e

stat : ∀ {M} → String → Expr M Scalar → Panel (prometheus M) Stat
stat t e = mkPanel1 t e

gauge : ∀ {M} → String → Expr M Scalar → Panel (prometheus M) Gauge
gauge t e = mkPanel1 t e

bargauge : ∀ {M} → String → Expr M Scalar → Panel (prometheus M) BarGauge
bargauge t e = mkPanel1 t e

table : ∀ {M} → String → Expr M InstantVector → Panel (prometheus M) Table
table t e = mkPanel1 t e

-- ─────────────────────────────────────────────────────────────────────
-- Decorazione fieldConfig: combinatori post-fix su Panel di qualunque
-- datasource/kind. `withUnit "ms" (timeseries …)`,
-- `withThresholds (mkThresholds "red" ((1.0 , "green") ∷ [])) (stat …)`.
-- ─────────────────────────────────────────────────────────────────────

withUnit : ∀ {ds k} → String → Panel ds k → Panel ds k
withUnit u p =
  record p { config = record (Panel.config p) { unit = just u } }

withThresholds : ∀ {ds k} → Thresholds → Panel ds k → Panel ds k
withThresholds th p =
  record p { config = record (Panel.config p) { thresholds = just th } }

-- Registra le variabili di dashboard referenziate dai target del panel
-- (entrano nella raccolta `collectPanelVars` e quindi nel templating e
-- nella well-formedness): `withVars (envVar ∷ []) (timeseries …)`.
withVars : ∀ {ds k} → List Variable → Panel ds k → Panel ds k
withVars vs p = record p { vars = vs }

-- ─────────────────────────────────────────────────────────────────────
-- Operatori infissi: ↕ è hcut (top sopra bot), ↔ è vcut (left accanto
-- a right). Pura ri-denominazione, content-poli e *universe-poli* in C.
-- Precedenza: ↔ (6) lega più stretto di ↕ (5).
-- ─────────────────────────────────────────────────────────────────────

_↕_ : ∀ {ℓ} {C : Set ℓ} {x y w ht hb}
    → Tiling C x y w (suc ht)
    → Tiling C x (y + suc ht) w (suc hb)
    → Tiling C x y w (suc ht + suc hb)
_↕_ = hcut
infixr 5 _↕_

_↔_ : ∀ {ℓ} {C : Set ℓ} {x y h wl wr}
    → Tiling C x y (suc wl) h
    → Tiling C (x + suc wl) y (suc wr) h
    → Tiling C x y (suc wl + suc wr) h
_↔_ = vcut
infixr 6 _↔_

-- ─────────────────────────────────────────────────────────────────────
-- Widget: tassellamento autosufficiente con footprint nel tipo,
-- piazzabile a qualunque (x, y). Universe-polimorfo in C.
-- ─────────────────────────────────────────────────────────────────────

Widget : ∀ {ℓ} → Set ℓ → ℕ → ℕ → Set ℓ
Widget C w h = ∀ {x y} → Tiling C x y w h

-- ─────────────────────────────────────────────────────────────────────
-- Aritmetica di stack.
-- ─────────────────────────────────────────────────────────────────────

private
  stackH-inner : ℕ → ℕ → ℕ
  stackH-inner zero    h = h
  stackH-inner (suc n) h = h + suc (stackH-inner n h)

  stackW-inner : ℕ → ℕ → ℕ
  stackW-inner zero    w = w
  stackW-inner (suc n) w = w + suc (stackW-inner n w)

stackH : ℕ → ℕ → ℕ
stackH n h = suc (stackH-inner n h)

stackW : ℕ → ℕ → ℕ
stackW n w = suc (stackW-inner n w)

-- ─────────────────────────────────────────────────────────────────────
-- rows / cols: combinatori n-ari per decomposizione EQUA.
-- ─────────────────────────────────────────────────────────────────────

rows : ∀ {ℓ} {C : Set ℓ} {w h n}
     → Vec (Widget C w (suc h)) (suc n) → Widget C w (stackH n h)
rows (t ∷ [])     = t
rows (t ∷ u ∷ us) = t ↕ rows (u ∷ us)

cols : ∀ {ℓ} {C : Set ℓ} {w h n}
     → Vec (Widget C (suc w) h) (suc n) → Widget C (stackW n w) h
cols (t ∷ [])     = t
cols (t ∷ u ∷ us) = t ↔ cols (u ∷ us)

-- ─────────────────────────────────────────────────────────────────────
-- Binder per template variables.
-- ─────────────────────────────────────────────────────────────────────

forEach : (name : String) (opts : List⁺ String)
        → (f : Variable → Dashboard)
        → {wf : T (varsConsistentB
                    (collectPanelVars (Dashboard.tiling (f (mkVariable name opts)))
                     ++
                     (mkVariable name opts ∷
                      Dashboard.variables (f (mkVariable name opts)))))}
        → Dashboard
forEach name opts f {wf} =
  let v = mkVariable name opts
      d = f v
  in mkDashboard (Dashboard.title d) (Dashboard.uid d)
                 (v ∷ Dashboard.variables d)
                 (Dashboard.viewport d) (Dashboard.tiling d) {wf}
