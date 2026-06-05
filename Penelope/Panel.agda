{-# OPTIONS --safe --without-K #-}

module Penelope.Panel where

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
