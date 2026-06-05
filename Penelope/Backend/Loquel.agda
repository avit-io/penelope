{-# OPTIONS --safe --without-K #-}

module Penelope.Backend.Loquel where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Loquel backend per Penelope. Loquel è l'astrazione neutra che     ║
-- ║  copre Loki ed Elastic: UNA QueryLang sola, DUE Datasource         ║
-- ║  (`loki s`, `elastic s`). Una stessa query Loquel può essere       ║
-- ║  impacchettata in un panel su `loki s` e in un altro su            ║
-- ║  `elastic s`: il render risultante usa due frammenti distinti      ║
-- ║  (LogQL via Loquel.Render.LogQL vs JSON via Loquel.Render.Elastic).║
-- ║                                                                    ║
-- ║  `faithful?` PER PANEL: ogni datasource usa il proprio frammento   ║
-- ║  fedele (faithfulLogQLB / faithfulElasticB). Una pipe non fedele   ║
-- ║  rifiuta il typecheck nel panel su quel datasource.                ║
-- ║                                                                    ║
-- ║  Il LQKind classifica i tre "ruoli" che una query Loquel ricopre:  ║
-- ║   • scalarM   → Stat/Gauge/BarGauge   (instantanea)                ║
-- ║   • rangeM    → TimeSeries            (con finestra)               ║
-- ║   • logStream → Table                 (log lines)                  ║
-- ║                                                                    ║
-- ║  Il `Ctx` (lo schema Loquel di partenza) compare via Lift perché   ║
-- ║  QueryLang.Ctx è in Set₁ ma Schema vive in Set.                    ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Level                       using (Level; Lift; lift; lower)
open import Data.Bool                   using (Bool)
open import Data.List                   using (List)
open import Data.String                 using (String)

open import Loquel.Schema               using (Schema)
open import Loquel.Pipe                 using (Pipe)
open import Loquel.Render.LogQL         using (renderLogQL; MetricKind;
                                               LogQLWindow; renderMetricLogQL)
open import Loquel.Render.Elastic       using (renderElastic)
open import Loquel.Render.Faithful      using (faithfulLogQLB; faithfulElasticB)
open import Loquel.Render.JSON          using (serialize)

open import Penelope.Panel
open import Penelope.Query
open import Penelope.Datasource

-- I tre ruoli che una query Loquel ricopre in un panel.
data LQKind : Set where
  scalarM   : LQKind
  rangeM    : LQKind
  logStream : LQKind

loquelQueryTypeOf : PanelKind → LQKind
loquelQueryTypeOf Stat       = scalarM
loquelQueryTypeOf Gauge      = scalarM
loquelQueryTypeOf BarGauge   = scalarM
loquelQueryTypeOf TimeSeries = rangeM
loquelQueryTypeOf Table      = logStream

-- Ctx Loquel: lo schema di partenza, lifted in Set₁ per uniformità con
-- QueryLang.Ctx.
CtxL : Set₁
CtxL = Lift _ Schema

-- La query Loquel impacchetta una Pipe (con i suoi schemi esistenziali)
-- più i metadati specifici del ruolo:
--   • scalarM:   Pipe + MetricKind + by-labels.
--   • rangeM:    Pipe + MetricKind + by-labels + finestra.
--   • logStream: Pipe pura.
-- Lo schema di partenza `a` è parametro; il secondo schema `b` resta
-- esistenziale: ad ogni stadio Loquel ne cambia la forma, ma da
-- Penelope non lo guardiamo.
data LoquelTarget' (a : Schema) : LQKind → Set where
  scalarT : ∀ {b} → Pipe a b → MetricKind → List String
          → LoquelTarget' a scalarM
  rangeT  : ∀ {b} → Pipe a b → MetricKind → List String → LogQLWindow
          → LoquelTarget' a rangeM
  logT    : ∀ {b} → Pipe a b
          → LoquelTarget' a logStream

-- Surface a livello CtxL: scarta il Lift per riallinearsi a Schema.
-- Resta a Set perché LoquelTarget' lo è.
LoquelTarget : CtxL → LQKind → Set
LoquelTarget c τ = LoquelTarget' (lower c) τ

Loquel : QueryLang
Loquel = record
  { Ctx         = CtxL
  ; QueryType   = LQKind
  ; Query       = LoquelTarget
  ; queryTypeOf = loquelQueryTypeOf
  }

-- ─── Loki datasource ────────────────────────────────────────────────

renderLoki : ∀ {c τ} → LoquelTarget c τ → String
renderLoki (logT p)              = renderLogQL p
renderLoki (rangeT  p k by w)    = renderMetricLogQL p k by w
renderLoki (scalarT p k by)      = renderMetricLogQL p k by "1m"

faithfulLoki?B : ∀ {c τ} → LoquelTarget c τ → Bool
faithfulLoki?B (logT p)              = faithfulLogQLB p
faithfulLoki?B (rangeT  p _ _ _)     = faithfulLogQLB p
faithfulLoki?B (scalarT p _ _)       = faithfulLogQLB p

loki : Schema → Datasource
loki s = record
  { lang        = Loquel
  ; ctx         = lift s
  ; grafanaType = "loki"
  ; render      = renderLoki
  ; faithful?   = faithfulLoki?B
  }

-- ─── Elastic datasource ─────────────────────────────────────────────

renderElasticS : ∀ {c τ} → LoquelTarget c τ → String
renderElasticS (logT p)          = serialize (renderElastic p)
renderElasticS (rangeT  p _ _ _) = serialize (renderElastic p)
renderElasticS (scalarT p _ _)   = serialize (renderElastic p)

faithfulElastic?B : ∀ {c τ} → LoquelTarget c τ → Bool
faithfulElastic?B (logT p)          = faithfulElasticB p
faithfulElastic?B (rangeT  p _ _ _) = faithfulElasticB p
faithfulElastic?B (scalarT p _ _)   = faithfulElasticB p

elastic : Schema → Datasource
elastic s = record
  { lang        = Loquel
  ; ctx         = lift s
  ; grafanaType = "elasticsearch"
  ; render      = renderElasticS
  ; faithful?   = faithfulElastic?B
  }
