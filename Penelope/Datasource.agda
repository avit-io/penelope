{-# OPTIONS --safe --without-K #-}

module Penelope.Datasource where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Datasource — il backend concreto di una query.                    ║
-- ║                                                                    ║
-- ║  In Grafana il datasource è PER-PANEL (una dashboard può           ║
-- ║  mescolare Prometheus, Loki, Elastic, …). Quindi Datasource non    ║
-- ║  è parametro di Layout/Dashboard: a impacchettarlo è AnyPanel.     ║
-- ║                                                                    ║
-- ║  Campi:                                                            ║
-- ║   • lang        : la QueryLang del backend;                        ║
-- ║   • ctx         : il contesto concreto (Model, Schema, …);         ║
-- ║   • grafanaType : la stringa che Grafana usa come `datasource.type`║
-- ║                   (es. "prometheus", "loki", "elasticsearch");     ║
-- ║   • render      : un renderer totale Query → String;               ║
-- ║   • faithful?   : un predicato booleano "questa query sta nel      ║
-- ║                   frammento fedele del backend?". Per Loquel viene ║
-- ║                   da Loquel.Render.Faithful; per HenQL è            ║
-- ║                   vacuamente true.                                 ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Penelope.Query

open import Data.Bool   using (Bool)
open import Data.String using (String)

record Datasource : Set₂ where
  field
    lang        : QueryLang
    ctx         : QueryLang.Ctx lang
    grafanaType : String
    render      : ∀ {τ} → QueryLang.Query lang ctx τ → String
    faithful?   : ∀ {τ} → QueryLang.Query lang ctx τ → Bool
