module Penelope.JSON where

open import Prometea.Core
open import HenQL.Syntax
open import HenQL.Print
open import Penelope.Panel
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

  renderTarget : {M : Model} {τ : PromType} → Expr M τ → String
  renderTarget e = "{ \"expr\": \"" ++ prettyExpr e ++ "\" }"

  renderTargetTail : {M : Model} {τ : PromType} → List (Expr M τ) → String
  renderTargetTail []       = ""
  renderTargetTail (e ∷ es) = ", " ++ renderTarget e ++ renderTargetTail es

  renderTargets : {M : Model} {τ : PromType} → List⁺ (Expr M τ) → String
  renderTargets ts =
    "[" ++ renderTarget   (List⁺.head ts)
        ++ renderTargetTail (List⁺.tail ts)
        ++ "]"

  renderPanel : {M : Model} → Rect → AnyPanel M → String
  renderPanel pos (k , mkPanel ti tgs) =
    "    {"                                                              ++ nl ++
    "      \"type\": \"" ++ panelTypeOf k ++ "\","                        ++ nl ++
    "      \"title\": \"" ++ ti ++ "\","                                  ++ nl ++
    "      \"datasource\": { \"type\": \"prometheus\" },"                 ++ nl ++
    "      \"gridPos\": { \"x\": " ++ showℕ (x pos)
                     ++ ", \"y\": " ++ showℕ (y pos)
                     ++ ", \"w\": " ++ showℕ (w pos)
                     ++ ", \"h\": " ++ showℕ (h pos) ++ " },"            ++ nl ++
    "      \"targets\": " ++ renderTargets tgs                            ++ nl ++
    "    }"

  -- Walk del Tiling content-polimorfo, istanziato a C := AnyPanel M.
  -- Ad ogni tile, il payload è il panel da renderizzare; il gridPos è
  -- derivato dagli implicit (x y w h) del tile.
  walk : {M : Model} {x y w h : ℕ}
       → Tiling (AnyPanel M) x y w h → String
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

-- Render totale di una dashboard in Grafana JSON. I gridPos sono validi
-- per costruzione: ogni cella ha w ≥ 1, h ≥ 1, è contenuta nel viewport,
-- e non si sovrappone alle altre (lemmi `contained`/`disjoint` in Tiling).
-- Le template variables vengono emesse nel blocco "templating".
renderDashboard : {M : Model} → Dashboard M → String
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
-- disgiunzione.
-- ─────────────────────────────────────────────────────────────────────

renderDashboardCertified
  : {M : Model} (d : Dashboard M)
  → String
  × Σ (List Rect) (λ rs →
      All (_⊆ Dashboard.viewport d) rs × Pairwise Disjoint rs)
renderDashboardCertified d =
  renderDashboard d
  , placedRects (Dashboard.tiling d)
  , placedRects-contained (Dashboard.tiling d)
  , placedRects-disjoint  (Dashboard.tiling d)
