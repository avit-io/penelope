module Penelope.JSON where

open import Prometea.Core
open import HenQL.Syntax
open import HenQL.Print
open import Penelope.Panel
open import Penelope.Layout
open import Penelope.Dashboard

open import Data.Nat      using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String   using (String; _++_)
open import Data.Product  using (_,_)

private
  nl : String
  nl = "\n"

  -- Divisione per due, totale, per ricorsione strutturale.
  -- Evita la dipendenza da Data.Nat.DivMod (che richiede NonZero come istanza).
  halve : ℕ → ℕ
  halve zero          = zero
  halve (suc zero)    = zero
  halve (suc (suc n)) = suc (halve n)

  -- Posizione griglia in unità Grafana (24 colonne, h in row units).
  record GridPos : Set where
    constructor mkPos
    field
      gx gy gw gh : ℕ
  open GridPos

  panelTypeOf : PanelKind → String
  panelTypeOf TimeSeries = "timeseries"
  panelTypeOf Stat       = "stat"
  panelTypeOf Gauge      = "gauge"
  panelTypeOf Table      = "table"

  renderPanel : {M : Model} → GridPos → AnyPanel M → String
  renderPanel pos (k , mkPanel ti tg) =
    let q = prettyExpr tg in
      "    {"                                                              ++ nl ++
      "      \"type\": \"" ++ panelTypeOf k ++ "\","                        ++ nl ++
      "      \"title\": \"" ++ ti ++ "\","                                  ++ nl ++
      "      \"datasource\": { \"type\": \"prometheus\" },"                 ++ nl ++
      "      \"gridPos\": { \"x\": " ++ showℕ (gx pos)
                       ++ ", \"y\": " ++ showℕ (gy pos)
                       ++ ", \"w\": " ++ showℕ (gw pos)
                       ++ ", \"h\": " ++ showℕ (gh pos) ++ " },"            ++ nl ++
      "      \"targets\": [{ \"expr\": \"" ++ q ++ "\" }]"                  ++ nl ++
      "    }"

  -- Walk del BSP: ogni split divide il viewport in due regioni disgiunte
  -- e ricorre. Le foglie ricevono il GridPos derivato dalla loro posizione
  -- nell'albero. Le virgole fra panel sono iniettate dai nodi interni:
  -- per N foglie ci sono N-1 nodi → N-1 virgole, esattamente quante servono.
  walk : {M : Model} → GridPos → Layout M → String
  walk pos (cell p) = renderPanel pos p
  walk pos (above t b) =
    let hh   = halve (gh pos)
        topP = mkPos (gx pos) (gy pos)        (gw pos) hh
        botP = mkPos (gx pos) (gy pos + hh)   (gw pos) (gh pos ∸ hh)
    in walk topP t ++ "," ++ nl ++ walk botP b
  walk pos (beside l r) =
    let ww   = halve (gw pos)
        lftP = mkPos (gx pos)        (gy pos) ww             (gh pos)
        rgtP = mkPos (gx pos + ww)   (gy pos) (gw pos ∸ ww)  (gh pos)
    in walk lftP l ++ "," ++ nl ++ walk rgtP r

-- Render totale di una dashboard in Grafana JSON.
-- Viewport iniziale: 24 colonne × 16 row units (default schema Grafana).
renderDashboard : {M : Model} → Dashboard M → String
renderDashboard d =
  let panels = walk (mkPos 0 0 24 16) (Dashboard.canvas d) in
    "{"                                                ++ nl ++
    "  \"title\": \"" ++ Dashboard.title d ++ "\","     ++ nl ++
    "  \"uid\": \"" ++ Dashboard.uid d ++ "\","         ++ nl ++
    "  \"schemaVersion\": 39,"                          ++ nl ++
    "  \"panels\": ["                                   ++ nl ++
    panels                                              ++ nl ++
    "  ]"                                               ++ nl ++
    "}"
