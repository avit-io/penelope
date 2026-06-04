module Penelope.Sugar where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Zucchero sintattico per la composizione di dashboard.             ║
-- ║                                                                    ║
-- ║  Tutto qui sono DEFINIZIONI: si riducono ai costruttori esistenti  ║
-- ║  (tile, hcut, vcut, mkPanel) e al pairing Σ. Nessun nuovo data     ║
-- ║  type, nessuna prova ulteriore: gli invarianti del livello         ║
-- ║  geometrico (disgiunzione, contenimento, min-size, universali su   ║
-- ║  C) e quelli della decorazione (coerenza panel↔query, coerenza     ║
-- ║  del modello con C := AnyPanel M in Dashboard) si propagano        ║
-- ║  gratuitamente.                                                    ║
-- ║                                                                    ║
-- ║  ↕/↔ sono polimorfi in C: il modello M compare solo dove si        ║
-- ║  posiziona un panel via tile (□ ...).                              ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Prometea.Core
open import HenQL.Syntax
open import Penelope.Panel
open import Penelope.Tiling
open import Penelope.Variable  public
open import Penelope.Dashboard

open import Data.Nat           using (ℕ; zero; suc; _+_)
open import Data.Product       using (_,_)
open import Data.List          using (List; _∷_)
open import Data.List.NonEmpty using (List⁺; [_])
open import Data.Vec           using (Vec; _∷_; [])
open import Data.String        using (String)

-- ─────────────────────────────────────────────────────────────────────
-- □_: AnyPanel da Panel con kind implicito.
-- ─────────────────────────────────────────────────────────────────────

□_ : ∀ {M k} → Panel M k → AnyPanel M
□_ {k = k} p = k , p
infix 9 □_

-- ─────────────────────────────────────────────────────────────────────
-- Costruttori per-kind: titolo + target → Panel del kind appropriato.
-- ─────────────────────────────────────────────────────────────────────

timeseries : ∀ {M} → String → Expr M InstantVector → Panel M TimeSeries
timeseries t e = mkPanel t [ e ]

stat : ∀ {M} → String → Expr M Scalar → Panel M Stat
stat t e = mkPanel t [ e ]

gauge : ∀ {M} → String → Expr M Scalar → Panel M Gauge
gauge t e = mkPanel t [ e ]

bargauge : ∀ {M} → String → Expr M Scalar → Panel M BarGauge
bargauge t e = mkPanel t [ e ]

table : ∀ {M} → String → Expr M InstantVector → Panel M Table
table t e = mkPanel t [ e ]

-- ─────────────────────────────────────────────────────────────────────
-- Operatori infissi: ↕ è hcut (top sopra bot), ↔ è vcut (left accanto
-- a right). Pura ri-denominazione, content-poli in C.
-- Precedenza: ↔ (6) lega più stretto di ↕ (5).
-- ─────────────────────────────────────────────────────────────────────

_↕_ : ∀ {C x y w ht hb}
    → Tiling C x y w (suc ht)
    → Tiling C x (y + suc ht) w (suc hb)
    → Tiling C x y w (suc ht + suc hb)
_↕_ = hcut
infixr 5 _↕_

_↔_ : ∀ {C x y h wl wr}
    → Tiling C x y (suc wl) h
    → Tiling C (x + suc wl) y (suc wr) h
    → Tiling C x y (suc wl + suc wr) h
_↔_ = vcut
infixr 6 _↔_

-- ─────────────────────────────────────────────────────────────────────
-- Widget: tassellamento autosufficiente con footprint nel tipo,
-- piazzabile a qualunque (x, y). Content-polimorfo: AnyPanel compare
-- solo quando si istanzia C con un panel.
-- ─────────────────────────────────────────────────────────────────────

Widget : Set → ℕ → ℕ → Set
Widget C w h = ∀ {x y} → Tiling C x y w h

-- ─────────────────────────────────────────────────────────────────────
-- Aritmetica di stack — formulata in modo che il risultato sia SEMPRE
-- in suc-forma definizionalmente, anche per n variabile. Necessario
-- per far typecheckare `t ↕ rest` dove rest ha altezza `stackH m h`:
-- il lato bot di ↕ richiede `suc hb`, che con suc esterno si unifica.
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
--
-- N.B. ↕/↔ restano i primitivi PESATI (altezze/larghezze arbitrarie via
-- tipo); rows/cols sono solo la comodità n-aria equa. A ↔ B ↔ C
-- associativo a destra è A ↔ (B ↔ C) — A prende metà, B e C l'altra
-- metà: NON sono tre colonne uguali. Per quello servono cols n-ario.
-- ─────────────────────────────────────────────────────────────────────

rows : ∀ {C w h n} → Vec (Widget C w (suc h)) (suc n) → Widget C w (stackH n h)
rows (t ∷ [])     = t
rows (t ∷ u ∷ us) = t ↕ rows (u ∷ us)

cols : ∀ {C w h n} → Vec (Widget C (suc w) h) (suc n) → Widget C (stackW n w) h
cols (t ∷ [])     = t
cols (t ∷ u ∷ us) = t ↔ cols (u ∷ us)

-- ─────────────────────────────────────────────────────────────────────
-- Binder per template variables.
-- ─────────────────────────────────────────────────────────────────────

forEach : ∀ {M} → String → List⁺ String
        → (Variable → Dashboard M) → Dashboard M
forEach name opts f =
  let v = mkVariable name opts
      d = f v
  in record d { variables = v ∷ Dashboard.variables d }
