{-# OPTIONS --safe --without-K #-}

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  Il ponte semeion → Penelope.                                         ║
-- ║                                                                        ║
-- ║  semeion produce la scelta GIÀ DIMOSTRATA come `Display` (la           ║
-- ║  primitiva geometrica). Qui Penelope — la tessitrice — la traduce nel  ║
-- ║  `PanelKind` di Grafana. Il nome del pannello è l'epifenomeno della    ║
-- ║  forma: non c'è scelta in questo modulo, solo una traduzione 1-1.      ║
-- ║                                                                        ║
-- ║  Garanzia: `panelKind` è una BIIEZIONE (round-trip provati). Geometria ║
-- ║  e panel kind portano la stessa informazione — nessuna forma si perde, ║
-- ║  nessun widget è inventato.                                            ║
-- ╚══════════════════════════════════════════════════════════════════════╝

module Penelope.Semeion where

open import Penelope.Panel
  using (PanelKind; TimeSeries; Stat; Gauge; BarGauge; Table; StatusHistory)
open import Semeion.Signal
  using ( Display; arc; bars; number; line; stateBands; grid
        ; Faithful; forced; underdetermined )

open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ── L'adapter: ogni primitiva geometrica È un panel kind ───────────────
panelKind : Display → PanelKind
panelKind arc        = Gauge
panelKind bars       = BarGauge
panelKind number     = Stat
panelKind line       = TimeSeries
panelKind stateBands = StatusHistory
panelKind grid       = Table

-- ── Da una lettura semeion al panel kind ───────────────────────────────
-- `forced` ⇒ il kind dimostrato. `underdetermined` ⇒ NIENTE: una lettura
-- sottodeterminata non si rende senza prima pagare la stipulazione.
-- L'onestà nel tipo di semeion si propaga fino a Penelope.
panelKindOf : Faithful → Maybe PanelKind
panelKindOf (forced d)          = just (panelKind d)
panelKindOf (underdetermined _) = nothing

-- ── L'inverso, e la prova che è una biiezione ──────────────────────────
displayOf : PanelKind → Display
displayOf TimeSeries    = line
displayOf Stat          = number
displayOf Gauge         = arc
displayOf BarGauge      = bars
displayOf Table         = grid
displayOf StatusHistory = stateBands

display-round : ∀ d → displayOf (panelKind d) ≡ d
display-round arc        = refl
display-round bars       = refl
display-round number     = refl
display-round line       = refl
display-round stateBands = refl
display-round grid       = refl

panelKind-round : ∀ k → panelKind (displayOf k) ≡ k
panelKind-round TimeSeries    = refl
panelKind-round Stat          = refl
panelKind-round Gauge         = refl
panelKind-round BarGauge      = refl
panelKind-round Table         = refl
panelKind-round StatusHistory = refl
