module Penelope.JSON where

open import Prometea.Core
open import HenQL.Syntax
open import HenQL.Print
open import Penelope.Panel
open import Penelope.Tiling
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

  -- Walk del Tiling: ad ogni foglia, il Rect è derivato dagli indici del
  -- sotto-Tiling (place ≅ ricostruzione del Rect dalle implicite). Le
  -- virgole fra panel sono iniettate dai nodi interni: N foglie → N-1
  -- nodi → N-1 virgole, esattamente quante servono.
  walk : {M : Model} {x y w h : ℕ}
       → (t : Tiling x y w h)
       → (Leaf t → AnyPanel M)
       → String
  walk {x = x} {y = y} {w = w} {h = h} tile label =
    renderPanel (mkRect x y w h) (label here)
  walk (hcut tt tb) label =
    walk tt (λ l → label (topL l)) ++ "," ++ nl ++
    walk tb (λ l → label (botL l))
  walk (vcut tl tr) label =
    walk tl (λ l → label (leftL l)) ++ "," ++ nl ++
    walk tr (λ l → label (rightL l))

-- Render totale di una dashboard in Grafana JSON. I gridPos sono validi
-- per costruzione: ogni cella ha w ≥ 1, h ≥ 1 (struttura del Tiling),
-- è contenuta nel viewport (lemma `contained`), e non si sovrappone
-- alle altre (lemma `disjoint`).
renderDashboard : {M : Model} → Dashboard M → String
renderDashboard d =
  let panels = walk (Dashboard.tiling d) (Dashboard.label d) in
    "{"                                                ++ nl ++
    "  \"title\": \"" ++ Dashboard.title d ++ "\","     ++ nl ++
    "  \"uid\": \"" ++ Dashboard.uid d ++ "\","         ++ nl ++
    "  \"schemaVersion\": 39,"                          ++ nl ++
    "  \"panels\": ["                                   ++ nl ++
    panels                                              ++ nl ++
    "  ]"                                               ++ nl ++
    "}"

-- ─────────────────────────────────────────────────────────────────────
-- Render "certificato": il JSON insieme alla prova che i rettangoli
-- piazzati sono contenuti nel viewport e pairwise disgiunti. Permette
-- ai consumer downstream di ragionare sull'output, non solo sull'input.
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
