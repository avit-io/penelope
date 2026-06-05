{-# OPTIONS --safe --without-K #-}

module Penelope.Dashboard where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Target, Panel, AnyPanel, Dashboard.                               ║
-- ║                                                                    ║
-- ║  Un Panel porta una LISTA NON VUOTA di Target dello stesso         ║
-- ║  datasource e dello stesso kind. Ogni target è una query nel       ║
-- ║  QueryLang del datasource del panel, più decorazioni opzionali     ║
-- ║  (alias di serie, flag hidden). Il `refId` Grafana non si          ║
-- ║  memorizza: si deriva dalla posizione al render (0 → "A", 1 → …).  ║
-- ║                                                                    ║
-- ║  La fedeltà al frammento del backend è richiesta PER TARGET via    ║
-- ║  `ok : T (faithful? ds query)`. Una query fuori dal frammento      ║
-- ║  fedele NON typeckecka.                                            ║
-- ║                                                                    ║
-- ║  Multi-target ≠ multi-datasource: tutti i target di un panel       ║
-- ║  condividono il datasource del panel. Il pannello "-- Mixed --"    ║
-- ║  di Grafana non è in scope.                                        ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Penelope.Panel
open import Penelope.Query
open import Penelope.Datasource
open import Penelope.Tiling
open import Penelope.Variable

open import Data.Bool          using (T; Bool; false)
open import Data.List          using (List)
open import Data.List.NonEmpty using (List⁺; [_])
open import Data.Maybe         using (Maybe; nothing)
open import Data.String        using (String)
open import Data.Unit          using (tt)

-- Un singolo target di un Panel: una query (nel QueryLang del ds) più
-- decorazioni di serie. La fedeltà è imposta dal campo `ok`.
record Target (ds : Datasource) (k : PanelKind) : Set where
  constructor mkTarget
  field
    query  : QueryLang.Query (Datasource.lang ds) (Datasource.ctx ds)
               (QueryLang.queryTypeOf (Datasource.lang ds) k)
    alias  : Maybe String
    hidden : Bool
    ok     : T (Datasource.faithful? ds query)

-- Un panel sotto un datasource specifico, con lista NON VUOTA di target.
record Panel (ds : Datasource) (k : PanelKind) : Set where
  constructor mkPanel
  field
    title   : String
    targets : List⁺ (Target ds k)

-- Convenience: un panel single-target. L'`ok` è implicito perché per i
-- frammenti vacui (Prometheus) `T true` riduce a `⊤` che ha eta;
-- per Loquel l'utente lo passa esplicitamente come `{ok = tt}`.
mkPanel1 : ∀ {ds k}
         → (title : String)
         → (q : QueryLang.Query (Datasource.lang ds) (Datasource.ctx ds)
                  (QueryLang.queryTypeOf (Datasource.lang ds) k))
         → {ok : T (Datasource.faithful? ds q)}
         → Panel ds k
mkPanel1 {ds} {k} t q {ok} = record
  { title   = t
  ; targets = [ mkTarget q nothing false ok ]
  }

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
