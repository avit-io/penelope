{-# OPTIONS --safe --without-K #-}

module Penelope.JSON where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Render totale di una Dashboard in Grafana JSON.                   ║
-- ║                                                                    ║
-- ║  Il datasource è PER-PANEL: cammino la tela BSP e per ogni foglia  ║
-- ║  uso il Datasource impacchettato in AnyPanel per:                  ║
-- ║   • emettere il campo `datasource.type` (= grafanaType ds);        ║
-- ║   • renderizzare la target via (Datasource.render ds).             ║
-- ║                                                                    ║
-- ║  Resta totale per costruzione: i gridPos derivano dagli implicit   ║
-- ║  (x y w h) del tile, e i lemmi contained/disjoint in Tiling ci     ║
-- ║  garantiscono che ogni cella è nel viewport e nessuna si           ║
-- ║  sovrappone.                                                       ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Penelope.Panel
open import Penelope.Query
open import Penelope.Datasource
open import Penelope.Tiling
open import Penelope.Variable
open import Penelope.Dashboard

open import Data.Nat      using (ℕ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String   using (String; _++_)
open import Data.Product  using (Σ; _,_; _×_)
open import Data.List     using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺)
open import Data.List.Relation.Unary.All using (All)

private
  nl : String
  nl = "\n"

  panelTypeOf : PanelKind → String
  panelTypeOf TimeSeries = "timeseries"
  panelTypeOf Stat       = "stat"
  panelTypeOf Gauge      = "gauge"
  panelTypeOf BarGauge   = "bargauge"
  panelTypeOf Table      = "table"

  -- Render di un singolo target via il render del Datasource di quel panel.
  renderTargets : (ap : AnyPanel) → String
  renderTargets ap =
    let ds = AnyPanel.ds ap
        p  = AnyPanel.panel ap in
    "[{ \"expr\": \""
      ++ Datasource.render ds (Panel.target p)
      ++ "\" }]"

  renderPanel : Rect → AnyPanel → String
  renderPanel pos ap =
    let ds = AnyPanel.ds ap
        k  = AnyPanel.kind ap
        p  = AnyPanel.panel ap in
    "    {"                                                                ++ nl ++
    "      \"type\": \"" ++ panelTypeOf k ++ "\","                          ++ nl ++
    "      \"title\": \"" ++ Panel.title p ++ "\","                         ++ nl ++
    "      \"datasource\": { \"type\": \""
       ++ Datasource.grafanaType ds ++ "\" },"                              ++ nl ++
    "      \"gridPos\": { \"x\": " ++ showℕ (x pos)
                     ++ ", \"y\": " ++ showℕ (y pos)
                     ++ ", \"w\": " ++ showℕ (w pos)
                     ++ ", \"h\": " ++ showℕ (h pos) ++ " },"               ++ nl ++
    "      \"targets\": " ++ renderTargets ap                               ++ nl ++
    "    }"

  -- Walk del Tiling content-polimorfo, istanziato a C := AnyPanel.
  walk : {x y w h : ℕ} → Tiling AnyPanel x y w h → String
  walk {x = x} {y = y} {w = w} {h = h} (tile p) =
    renderPanel (mkRect x y w h) p
  walk (hcut tt tb) = walk tt ++ "," ++ nl ++ walk tb
  walk (vcut tl tr) = walk tl ++ "," ++ nl ++ walk tr

  -- ─── Template variables → blocco templating Grafana ───────────────

  renderVarOption : String → String
  renderVarOption v =
    "{ \"text\": \"" ++ v ++ "\", \"value\": \"" ++ v ++ "\" }"

  renderVarOptionsTail : List String → String
  renderVarOptionsTail []       = ""
  renderVarOptionsTail (v ∷ vs) =
    ", " ++ renderVarOption v ++ renderVarOptionsTail vs

  renderVarOptions : List⁺ String → String
  renderVarOptions opts =
    "[" ++ renderVarOption     (List⁺.head opts)
        ++ renderVarOptionsTail (List⁺.tail opts)
        ++ "]"

  varQueryString : List⁺ String → String
  varQueryString opts = go (List⁺.head opts) (List⁺.tail opts)
    where
      go : String → List String → String
      go h []       = h
      go h (v ∷ vs) = h ++ "," ++ go v vs

  renderVariable : Variable → String
  renderVariable v =
    let opts = Variable.options v
        h    = List⁺.head opts in
    "{ \"name\": \"" ++ Variable.name v ++ "\""               ++
    ", \"type\": \"custom\""                                  ++
    ", \"query\": \"" ++ varQueryString opts ++ "\""          ++
    ", \"current\": { \"text\": \"" ++ h ++ "\", \"value\": \"" ++ h ++ "\" }" ++
    ", \"options\": " ++ renderVarOptions opts                ++
    " }"

  joinVars : List Variable → String
  joinVars []           = ""
  joinVars (v ∷ [])     = renderVariable v
  joinVars (v ∷ w ∷ vs) = renderVariable v ++ ", " ++ joinVars (w ∷ vs)

  renderTemplating : List Variable → String
  renderTemplating vars = "{ \"list\": [" ++ joinVars vars ++ "] }"

renderDashboard : Dashboard → String
renderDashboard d =
  let panels = walk (Dashboard.tiling d)
      tmpl   = renderTemplating (Dashboard.variables d) in
    "{"                                                ++ nl ++
    "  \"title\": \"" ++ Dashboard.title d ++ "\","     ++ nl ++
    "  \"uid\": \"" ++ Dashboard.uid d ++ "\","         ++ nl ++
    "  \"schemaVersion\": 39,"                          ++ nl ++
    "  \"templating\": " ++ tmpl ++ ","                 ++ nl ++
    "  \"panels\": ["                                   ++ nl ++
    panels                                              ++ nl ++
    "  ]"                                               ++ nl ++
    "}"

-- ─────────────────────────────────────────────────────────────────────
-- Render "certificato": JSON + Σ con prove list-level di contenimento e
-- disgiunzione (universalmente quantificate su C := AnyPanel, eredità
-- diretta dei lemmi in Penelope.Tiling).
-- ─────────────────────────────────────────────────────────────────────

renderDashboardCertified
  : (d : Dashboard)
  → String
  × Σ (List Rect) (λ rs →
      All (_⊆ Dashboard.viewport d) rs × Pairwise Disjoint rs)
renderDashboardCertified d =
  renderDashboard d
  , placedRects (Dashboard.tiling d)
  , placedRects-contained (Dashboard.tiling d)
  , placedRects-disjoint  (Dashboard.tiling d)
