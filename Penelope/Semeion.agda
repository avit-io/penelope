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
open import Penelope.Datasource using (Datasource)
open import Penelope.Dashboard  using (Panel; Target; mkPanelT)
open import Semeion.Signal
  using ( Display; arc; bars; number; line; stateBands; grid
        ; Faithful; forced; underdetermined
        ; Signal; mkSignal; ratio; flow; point; comparable; Ratio
        ; Intent; now; displayAt )

open import Data.List.NonEmpty using (List⁺)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.String        using (String)
open import Data.Empty         using (⊥)
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

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  PORTA 1 — il kind FORZATO dal segnale (non più un implicito libero). ║
-- ║                                                                        ║
-- ║  Oggi `Panel ds k` ha `k` libero: puoi scrivere `Panel ds Gauge` su   ║
-- ║  un `flow`. L'adapter lo SMENTISCE, ma non lo IMPEDISCE. Qui il kind   ║
-- ║  diventa funzione del segnale: l'unico modo di ottenere il pannello è  ║
-- ║  esibire la derivazione `displayAt i s ≡ forced d`.                   ║
-- ║                                                                        ║
-- ║  Limite (onesto): questo lega kind ↔ Signal, NON Signal ↔ query. Il   ║
-- ║  `Signal` resta asserito a fianco dei Target — chiuderlo è «porta 2»  ║
-- ║  (costruttori-query geometrici), non derivabile dalla sintassi.       ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- Il tipo del costruttore, CALCOLATO dal segnale: forced ⇒ builder del kind
-- emerso; underdetermined ⇒ ⊥ (non costruibile, per costruzione).
PanelFor : Datasource → Intent → Signal → Set
PanelFor ds i s with displayAt i s
... | forced d          = List⁺ (Target ds (panelKind d)) → Panel ds (panelKind d)
... | underdetermined _ = ⊥

-- Il costruttore forzato: il kind non si passa, si deriva. La prova
-- `displayAt i s ≡ forced d` è il cancello — senza, niente pannello. Un
-- segnale underdetermined non ammette `d` con `forced d`: non typecheck.
panelOf : ∀ {ds} (i : Intent) (s : Signal) {d : Display}
        → displayAt i s ≡ forced d
        → String → List⁺ (Target ds (panelKind d)) → Panel ds (panelKind d)
panelOf i s _ title ts = mkPanelT title ts

-- Il fiat CONFINATO e VISIBILE: quando scegli un kind senza che emerga
-- (segnale sottodeterminato, o fuori-geometria), lo dici col nome. Nessun
-- teorema dietro — è regime 3, e si vede. `mkPanelT`/`mkPanel1` col `{k}`
-- libero restano l'API grezza, da relegare a questo caso.
panelStipulated : ∀ {ds} (k : PanelKind) → String → List⁺ (Target ds k) → Panel ds k
panelStipulated k title ts = mkPanelT title ts

-- ── La legge nei tipi ──────────────────────────────────────────────────
-- SLI adesso: PanelFor È il builder di Gauge — il widget emerge.
sliPanelEmerges : ∀ {ds} (r : Ratio)
  → PanelFor ds now (mkSignal (ratio r) point)
  ≡ (List⁺ (Target ds Gauge) → Panel ds Gauge)
sliPanelEmerges _ = refl

-- flow/comparable adesso (sottodeterminato): PanelFor È ⊥ — non costruibile.
flowFamilyNoPanel : ∀ {ds}
  → PanelFor ds now (mkSignal flow comparable) ≡ ⊥
flowFamilyNoPanel = refl
