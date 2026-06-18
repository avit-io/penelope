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
open import Data.Maybe  using (Maybe; just; nothing)
open import Data.String using (String; _++_)

record Datasource : Set₂ where
  field
    lang        : QueryLang
    ctx         : QueryLang.Ctx lang
    grafanaType : String
    -- `uid` Grafana del datasource: con `nothing` Grafana aggancia
    -- all'import il datasource di default per `grafanaType`; con
    -- `just u` il binding è esplicito (consigliato con più istanze).
    uid         : Maybe String
    render      : ∀ {τ} → QueryLang.Query lang ctx τ → String
    faithful?   : ∀ {τ} → QueryLang.Query lang ctx τ → Bool

-- Fissa l'uid di un datasource costruito dai backend (che lo lasciano
-- a `nothing`): `setUid "PBFA97CFB590B2093" (prometheus M)`.
setUid : String → Datasource → Datasource
setUid u d = record d { uid = just u }

-- ─── Datasource scelto all'import (`__inputs`) ───────────────────────
--
-- Un `DSInput` dichiara un datasource che Grafana fa SCEGLIERE ALL'IMPORT
-- (pattern delle dashboard condivisibili): all'import compare un selettore
-- "scegli il datasource <label>", poi `${name}` viene sostituito ovunque.
-- Nessun menù resta sulla dashboard. Pannelli/variabili lo referenziano
-- via `inputRef` (es. uid `${DS_PROMETHEUS}`).
record DSInput : Set where
  constructor mkDSInput
  field
    name     : String   -- token referenziato: es. "DS_PROMETHEUS"
    label    : String   -- etichetta nel dialog d'import: es. "Prometheus"
    pluginId : String   -- es. "prometheus"

-- Riferimento `${name}` da usare come uid (con setUid, o nei DSRef).
inputRef : DSInput → String
inputRef i = "${" ++ DSInput.name i ++ "}"
