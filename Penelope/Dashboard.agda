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
-- ║                                                                    ║
-- ║  Dashboard porta un VINCOLO DI BEN FORMAZIONE sulle variabili:     ║
-- ║  due riferimenti con lo stesso `name` ma `spec` divergenti (es.    ║
-- ║  multi=true vs multi=false, o `fld` diversi) sono un errore di    ║
-- ║  tipo (`varsConsistentB` riduce a `false` → `T false ≡ ⊥`).        ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Penelope.Panel
open import Penelope.Query
open import Penelope.Datasource
open import Penelope.Tiling
open import Penelope.Variable

open import Data.Bool          using (T; Bool; false; true)
open import Data.List          using (List; []; _∷_; _++_)
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
-- `vars` registra le variabili di dashboard referenziate dai target del
-- panel (i.e. quelle prodotte da `_==ᵛ_` nell'adapter Loquel o da `_=ᵛ_`
-- nell'adapter Prometheus). Sono opache qui — il render le raccoglie e
-- dedupplica per nome.
record Panel (ds : Datasource) (k : PanelKind) : Set where
  constructor mkPanel
  field
    title   : String
    targets : List⁺ (Target ds k)
    vars    : List Variable
    config  : FieldConfig

-- Convenience: un panel single-target. L'`ok` è implicito perché per i
-- frammenti vacui (Prometheus) `T true` riduce a `⊤` che ha eta;
-- per Loquel l'utente lo passa esplicitamente come `{ok = tt}`. Nessuna
-- variabile referenziata (`vars = []`).
mkPanel1 : ∀ {ds k}
         → (title : String)
         → (q : QueryLang.Query (Datasource.lang ds) (Datasource.ctx ds)
                  (QueryLang.queryTypeOf (Datasource.lang ds) k))
         → {ok : T (Datasource.faithful? ds q)}
         → Panel ds k
mkPanel1 {ds} {k} t q {ok} = record
  { title   = t
  ; targets = [ mkTarget q nothing false ok ]
  ; vars    = []
  ; config  = noConfig
  }

-- Esistenziale sul datasource (e sul kind).
record AnyPanel : Set₂ where
  constructor anyPanel
  field
    ds    : Datasource
    kind  : PanelKind
    panel : Panel ds kind

-- ─── Raccolta delle variable references dai panel sulla tela ─────────

collectPanelVars : ∀ {x y w h} → Tiling AnyPanel x y w h → List Variable
collectPanelVars (tile ap)     = Panel.vars (AnyPanel.panel ap)
collectPanelVars (hcut th tb′) = collectPanelVars th ++ collectPanelVars tb′
collectPanelVars (vcut tl tr)  = collectPanelVars tl ++ collectPanelVars tr

-- La dashboard: viewport + tela BSP + variabili-extra + ben formazione.
-- Tiling porta AnyPanel come contenuto, quindi panel con datasource
-- diversi possono coesistere nella stessa tela. Il campo `wf` è la prova
-- (implicita, di default `tt`) che le variabili — quelle raccolte dai
-- panel + quelle extra — sono COERENTI per nome (nessuna divergenza di
-- spec).
record Dashboard : Set₂ where
  constructor mkDashboard′
  field
    title     : String
    uid       : String
    variables : List Variable
    viewport  : Rect
    tiling    : TilingOf AnyPanel viewport
    wf        : T (varsConsistentB
                    (collectPanelVars tiling ++ variables))

-- Smart constructor: `wf` è implicito, l'utente non lo passa e si
-- risolve a `tt` quando la lista è coerente. Riferimenti in conflitto
-- (es. due `env` con `multi` diverso) ⇒ `T false ≡ ⊥`: typecheck fail.
mkDashboard : (title uid : String) (variables : List Variable)
            → (viewport : Rect) → (tl : TilingOf AnyPanel viewport)
            → {wf : T (varsConsistentB
                        (collectPanelVars tl ++ variables))}
            → Dashboard
mkDashboard t u vs vp tl {wf} = record
  { title     = t
  ; uid       = u
  ; variables = vs
  ; viewport  = vp
  ; tiling    = tl
  ; wf        = wf
  }
