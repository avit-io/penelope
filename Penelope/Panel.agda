{-# OPTIONS --safe --without-K #-}

module Penelope.Panel where

open import Data.Bool    using (Bool; true; false)
open import Data.Float   using (Float)
open import Data.List    using (List; [])
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ)
open import Data.Product using (_×_)
open import Data.String  using (String)
open import Data.Unit    using (⊤; tt)

-- Le famiglie di panel Grafana che Penelope sa tessere.
-- Il PromType / LQKind / … che ogni kind esige è ora un campo della
-- QueryLang associata al backend, non un dato fissato qui.
data PanelKind : Set where
  TimeSeries    : PanelKind
  Stat          : PanelKind
  Gauge         : PanelKind
  BarGauge      : PanelKind
  Table         : PanelKind
  -- status-history: traccia i cambi di valore nel tempo (es. health
  -- check FAIL/OK). Per Penelope la query è time-series (range/instant);
  -- il "group" Grafana è "status-history" lato JSON.
  StatusHistory : PanelKind

-- ─── Decorazione visiva (fieldConfig.defaults di Grafana) ────────────
--
-- Soglie: un colore base più step (soglia, colore) crescenti. Lato JSON
-- diventano `thresholds.steps` con il primo step a `value: null`.
record Thresholds : Set where
  constructor mkThresholds
  field
    baseColor : String
    steps     : List (Float × String)

-- Config di campo CONDIVISA da ogni kind (fieldConfig.defaults): unità
-- di misura (id Grafana: "ms", "percent", "reqps", "short", …) e soglie.
-- Due opzionali genuini, universali: niente a che vedere con le opzioni
-- specifiche di un kind, che vivono in `Viz` qui sotto.
record FieldConfig : Set where
  constructor mkFieldConfig
  field
    unit       : Maybe String
    thresholds : Maybe Thresholds

noConfig : FieldConfig
noConfig = mkFieldConfig nothing nothing

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Opzioni di visualizzazione INDICIZZATE SUL KIND.                  ║
-- ║                                                                    ║
-- ║  Il contesto (PanelKind) È la generalizzazione: ogni kind porta    ║
-- ║  ESATTAMENTE le manopole che ha. `Viz k` rende un'opzione assurda  ║
-- ║  — una TimeSeries con `colorMode`, una Stat con `fillOpacity` —    ║
-- ║  NON RAPPRESENTABILE: errore di tipo, non disciplina. Enum chiusi  ║
-- ║  (niente `Maybe String` da indovinare), render totale.            ║
-- ╚════════════════════════════════════════════════════════════════════╝

data ColorMode : Set where           -- Stat: come colorare il valore
  cmNone cmValue cmBackground : ColorMode

data GraphMode : Set where           -- Stat: sparkline o numero secco
  gmNone gmArea : GraphMode

data TextMode : Set where            -- Stat: cosa mostrare come testo
  tmAuto tmValue tmName tmNone : TextMode

data GradientMode : Set where        -- TimeSeries: gradiente del fill
  grNone grOpacity grHue grScheme : GradientMode

data BarDisplay : Set where          -- BarGauge: stile delle barre
  bdBasic bdGradient bdLcd : BarDisplay

record StatViz : Set where
  constructor mkStatViz
  field
    colorMode : ColorMode
    graphMode : GraphMode            -- gmArea ⇒ sparkline ⇒ query a range
    textMode  : TextMode

record TimeSeriesViz : Set where
  constructor mkTSViz
  field
    lineWidth    : ℕ
    fillOpacity  : ℕ                 -- 0..100
    gradientMode : GradientMode

record GaugeViz : Set where
  constructor mkGaugeViz
  field
    showThresholdMarkers : Bool

record BarGaugeViz : Set where
  constructor mkBarGaugeViz
  field
    display : BarDisplay

Viz : PanelKind → Set
Viz TimeSeries    = TimeSeriesViz
Viz Stat          = StatViz
Viz Gauge         = GaugeViz
Viz BarGauge      = BarGaugeViz
Viz Table         = ⊤
Viz StatusHistory = ⊤

-- Default per kind: ciò che un pannello «nudo» mostra finché non lo si
-- decora. Neutri (= default di Grafana) per non re-stilizzare di nascosto
-- le dashboard esistenti.
defaultViz : (k : PanelKind) → Viz k
defaultViz TimeSeries    = mkTSViz 1 0 grNone
defaultViz Stat          = mkStatViz cmValue gmNone tmAuto
defaultViz Gauge         = mkGaugeViz true
defaultViz BarGauge      = mkBarGaugeViz bdGradient
defaultViz Table         = tt
defaultViz StatusHistory = tt

-- L'`instant` del target è DERIVATO dal viz, non una manopola a sé: una
-- Stat con sparkline (gmArea) interroga un range (instant=false); senza,
-- legge l'ultimo valore (instant=true). Gauge/BarGauge: ultimo valore.
instantViz : (k : PanelKind) → Viz k → Bool
instantViz TimeSeries    _ = false
instantViz Stat          v = graphIsScalar (StatViz.graphMode v)
  where graphIsScalar : GraphMode → Bool
        graphIsScalar gmNone = true
        graphIsScalar gmArea = false
instantViz Gauge         _ = true
instantViz BarGauge      _ = true
instantViz Table         _ = false
instantViz StatusHistory _ = false
