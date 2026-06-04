module Penelope.Sugar where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Zucchero sintattico per la composizione di dashboard.             ║
-- ║                                                                    ║
-- ║  Tutto qui sono DEFINIZIONI: si riducono ai costruttori esistenti  ║
-- ║  (tile, hcut, vcut, mkPanel) e al pairing Σ. Nessun nuovo data     ║
-- ║  type, nessuna prova ulteriore: gli invarianti del livello         ║
-- ║  geometrico (disgiunzione, contenimento, min-size) e quelli della  ║
-- ║  decorazione (coerenza panel↔query, coerenza del modello) si       ║
-- ║  propagano gratuitamente.                                          ║
-- ║                                                                    ║
-- ║  Regola dello zucchero: definizioni sull'algebra, non estensioni.  ║
-- ║  Se aggiungessi un nuovo costruttore (es. un overlay) dovresti     ║
-- ║  ri-dimostrare disgiunzione e renderDashboard cesserebbe di essere ║
-- ║  totale gratis.                                                    ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Prometea.Core
open import HenQL.Syntax
open import Penelope.Panel
open import Penelope.Tiling
open import Penelope.Variable  public
open import Penelope.Dashboard

open import Data.Nat           using (ℕ; suc; _+_)
open import Data.Product       using (_,_)
open import Data.List          using (List; _∷_)
open import Data.List.NonEmpty using (List⁺; [_])
open import Data.String        using (String)

-- ─────────────────────────────────────────────────────────────────────
-- □_: AnyPanel da Panel con kind implicito.
--
-- Sostituisce il pattern (TimeSeries , errori) con (□ errori): il kind
-- è già nel tipo di `errori : Panel M TimeSeries`, ed è ridondante
-- ripeterlo nel costruttore di Σ.
-- ─────────────────────────────────────────────────────────────────────

□_ : ∀ {M k} → Panel M k → AnyPanel M
□_ {k = k} p = k , p
infix 9 □_

-- ─────────────────────────────────────────────────────────────────────
-- Costruttori per-kind: titolo + target → Panel del kind appropriato.
--
-- Sostituiscono il pattern `mkPanel "..." [ expr ]` (con annotazione di
-- tipo `: Panel M TimeSeries` lontana) con `timeseries "..." expr` —
-- il kind diventa leggibile inline. Sicurezza di tipo intatta: passare
-- un Expr di tipo sbagliato è errore di unificazione sulla chiamata,
-- perché la firma esige il tipo derivato da `queryTypeOf k`.
-- ─────────────────────────────────────────────────────────────────────

timeseries : ∀ {M} → String → Expr M InstantVector → Panel M TimeSeries
timeseries t e = mkPanel t [ e ]

stat : ∀ {M} → String → Expr M Scalar → Panel M Stat
stat t e = mkPanel t [ e ]

gauge : ∀ {M} → String → Expr M Scalar → Panel M Gauge
gauge t e = mkPanel t [ e ]

table : ∀ {M} → String → Expr M InstantVector → Panel M Table
table t e = mkPanel t [ e ]

-- ─────────────────────────────────────────────────────────────────────
-- Operatori infissi sul Tiling: ↕ è hcut (top sopra bot), ↔ è vcut
-- (left accanto a right). Pura ri-denominazione, stessa firma.
--
-- Precedenza: ↔ (6) lega più stretto di ↕ (5), così
--   A ↔ B ↕ C    parsa come   (A ↔ B) ↕ C.
-- Entrambi associativi a destra: A ↔ B ↔ C ≡ A ↔ (B ↔ C). Attenzione:
-- A ↔ B ↔ C NON è "tre colonne uguali" — A prende metà del rettangolo,
-- B e C si dividono l'altra metà. Per la decomposizione equa n-aria
-- serve `cols`/`rows` (roadmap).
--
-- I bracci di un cut hanno comunque indici di Tiling specifici (ht/hb
-- per ↕, wl/wr per ↔), quindi devono avere tipi annotati o derivabili
-- dal contesto. L'unificatore di Agda non risolve `suc n + suc n ≡ 16`
-- per `n` libero, quindi il single-expression senza annotazioni non
-- funziona — è il prezzo del livello geometrico intrinseco.
-- ─────────────────────────────────────────────────────────────────────

_↕_ : ∀ {x y w ht hb}
    → Tiling x y w (suc ht)
    → Tiling x (y + suc ht) w (suc hb)
    → Tiling x y w (suc ht + suc hb)
_↕_ = hcut
infixr 5 _↕_

_↔_ : ∀ {x y h wl wr}
    → Tiling x y (suc wl) h
    → Tiling (x + suc wl) y (suc wr) h
    → Tiling x y (suc wl + suc wr) h
_↔_ = vcut
infixr 6 _↔_

-- ─────────────────────────────────────────────────────────────────────
-- Binder per template variables.
--
-- `forEach name opts (λ v → body)` lega `v : Variable` nel corpo,
-- registra automaticamente la variabile nella dashboard prodotta. La
-- dashboard interna costruisce il proprio campo `variables` (tipicamente
-- vuoto), e forEach pre-pende la propria variabile. Componibile: più
-- forEach in cascata danno una dashboard con tutte le variabili
-- accumulate.
-- ─────────────────────────────────────────────────────────────────────

forEach : ∀ {M} → String → List⁺ String
        → (Variable → Dashboard M) → Dashboard M
forEach name opts f =
  let v = mkVariable name opts
      d = f v
  in record d { variables = v ∷ Dashboard.variables d }
