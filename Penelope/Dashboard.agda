{-# OPTIONS --safe --without-K #-}

module Penelope.Dashboard where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Panel, AnyPanel, Dashboard.                                       ║
-- ║                                                                    ║
-- ║  Un Panel è parametrizzato sul SUO Datasource (in Grafana il       ║
-- ║  datasource è per-panel, non per-dashboard). Il tipo della target  ║
-- ║  è derivato dal Datasource via il suo QueryLang: l'utente non      ║
-- ║  sceglie nulla — il typechecker impone Query (lang ds) (ctx ds)    ║
-- ║  (queryTypeOf (lang ds) k). Il campo `ok` è un T-witness che la    ║
-- ║  target sta nel frammento fedele del backend: per Prometheus è     ║
-- ║  vacuo (sempre true → ⊤), per Loquel diventa una ⊥ se la pipe      ║
-- ║  non è fedele, quindi è un *errore di tipo*.                       ║
-- ║                                                                    ║
-- ║  AnyPanel impacchetta esistenzialmente Datasource + PanelKind +    ║
-- ║  Panel. Tiling è universe-polimorfo, quindi può portare AnyPanel   ║
-- ║  (che vive a Set₂) come contenuto della tela BSP. Né Layout né     ║
-- ║  Dashboard hanno parametro Datasource: panel diversi nella stessa  ║
-- ║  tela possono avere datasource diversi.                            ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Penelope.Panel
open import Penelope.Query
open import Penelope.Datasource
open import Penelope.Tiling
open import Penelope.Variable

open import Data.Bool   using (T)
open import Data.List   using (List)
open import Data.String using (String)

-- Un panel sotto un datasource specifico.
record Panel (ds : Datasource) (k : PanelKind) : Set where
  constructor mkPanel
  field
    title  : String
    target : QueryLang.Query (Datasource.lang ds) (Datasource.ctx ds)
               (QueryLang.queryTypeOf (Datasource.lang ds) k)
    ok     : T (Datasource.faithful? ds target)

-- Esistenziale sul datasource (e sul kind).
record AnyPanel : Set₂ where
  constructor anyPanel
  field
    ds    : Datasource
    kind  : PanelKind
    panel : Panel ds kind

-- La dashboard: viewport + tela BSP + variables. Tiling porta AnyPanel
-- come contenuto, quindi panel con datasource diversi possono coesistere
-- nella stessa tela. Non c'è alcun parametro globale.
record Dashboard : Set₂ where
  constructor mkDashboard
  field
    title     : String
    uid       : String
    variables : List Variable
    viewport  : Rect
    tiling    : TilingOf AnyPanel viewport
