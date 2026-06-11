{-# OPTIONS --safe --without-K #-}

module Penelope.Panel where

open import Data.Float   using (Float)
open import Data.List    using (List; [])
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_×_)
open import Data.String  using (String)

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

-- Config di campo per panel: unità di misura (id Grafana: "ms",
-- "percent", "ops", "short", …) e soglie, entrambe opzionali.
record FieldConfig : Set where
  constructor mkFieldConfig
  field
    unit       : Maybe String
    thresholds : Maybe Thresholds

noConfig : FieldConfig
noConfig = mkFieldConfig nothing nothing
