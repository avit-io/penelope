{-# OPTIONS --safe --without-K #-}

module Penelope.JSON where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Render totale di una Dashboard in Grafana JSON.                   ║
-- ║                                                                    ║
-- ║  Il datasource è PER-PANEL: cammino la tela BSP e per ogni foglia  ║
-- ║  uso il Datasource impacchettato in AnyPanel per:                  ║
-- ║   • emettere il campo `datasource.type` (= grafanaType ds);        ║
-- ║   • renderizzare ogni target via (Datasource.render ds).           ║
-- ║                                                                    ║
-- ║  Un panel porta una lista NON VUOTA di Target. Il rendering        ║
-- ║  emette l'array `targets` con un elemento per Target, refId        ║
-- ║  derivato dalla posizione (0 → "A", 1 → "B", …), `alias` (se       ║
-- ║  presente) e flag `hidden`. La vizConfig resta unica per panel.    ║
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

open import Data.Bool     using (Bool; true; false)
open import Data.Char.Base using (Char) renaming (fromℕ to charFromℕ)
open import Data.Float.Base using (Float) renaming (show to showFloat)
open import Data.Maybe    using (Maybe; just; nothing; maybe)
open import Data.Nat      using (ℕ; suc; zero; _+_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String   using (String; _++_; fromList; toList; concat)
open import Data.Product  using (Σ; _,_; _×_)
open import Data.List     using (List; []; _∷_; map)
                          renaming (_++_ to _++ˡ_)
open import Data.List.NonEmpty using (List⁺; head; tail)
open import Data.List.Relation.Unary.All using (All)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
open import Relation.Nullary.Decidable.Core using (does)

private
  nl : String
  nl = "\n"

  -- Escaping JSON per stringhe arbitrarie: le query PromQL/Loquel
  -- contengono `"` nei label matcher; titoli e alias sono testo libero.
  escChar : Char → String
  escChar '"'  = "\\\""
  escChar '\\' = "\\\\"
  escChar '\n' = "\\n"
  escChar '\t' = "\\t"
  escChar c    = fromList (c ∷ [])

  escapeJSON : String → String
  escapeJSON s = concat (map escChar (toList s))

  panelTypeOf : PanelKind → String
  panelTypeOf TimeSeries    = "timeseries"
  panelTypeOf Stat          = "stat"
  panelTypeOf Gauge         = "gauge"
  panelTypeOf BarGauge      = "bargauge"
  panelTypeOf Table         = "table"
  panelTypeOf StatusHistory = "status-history"

  -- 0 → "A", 1 → "B", … (lettere maiuscole ASCII).
  refIdOf : ℕ → String
  refIdOf n = fromList (charFromℕ (65 + n) ∷ [])

  showBool : Bool → String
  showBool true  = "true"
  showBool false = "false"

  -- Campo `alias` opzionale: emesso solo se `just`.
  aliasField : Maybe String → String
  aliasField nothing  = ""
  aliasField (just a) = ", \"alias\": \"" ++ escapeJSON a ++ "\""

  -- L'instant è DERIVATO dal viz (instantViz): niente più chiavi da
  -- indovinare per-kind.
  instantField : Bool → String
  instantField true  = ", \"instant\": true"
  instantField false = ", \"instant\": false"

  -- reduceOptions: leggi "l'ultimo valore non nullo". Senza, Grafana
  -- ripiega su "mean" sull'intervallo (numeri mai osservati).
  reduceInner : String
  reduceInner =
    "\"reduceOptions\": { \"calcs\": [ \"lastNotNull\" ]"
      ++ ", \"fields\": \"\", \"values\": false }"

  -- ─── viz → stringhe Grafana (totali sugli enum chiusi) ────────────
  colorModeName : ColorMode → String
  colorModeName cmNone       = "none"
  colorModeName cmValue      = "value"
  colorModeName cmBackground = "background"

  graphModeName : GraphMode → String
  graphModeName gmNone = "none"
  graphModeName gmArea = "area"

  textModeName : TextMode → String
  textModeName tmAuto  = "auto"
  textModeName tmValue = "value"
  textModeName tmName  = "name"
  textModeName tmNone  = "none"

  gradientName : GradientMode → String
  gradientName grNone    = "none"
  gradientName grOpacity = "opacity"
  gradientName grHue     = "hue"
  gradientName grScheme  = "scheme"

  barDisplayName : BarDisplay → String
  barDisplayName bdBasic    = "basic"
  barDisplayName bdGradient = "gradient"
  barDisplayName bdLcd      = "lcd"

  -- `options` del pannello, per-kind, derivato dal Viz. Linea con
  -- newline da inserire nel panel; vuota per i kind senza options.
  optionsField : (k : PanelKind) → Viz k → String
  optionsField TimeSeries    _ = ""
  optionsField Table         _ = ""
  optionsField StatusHistory _ = ""
  optionsField Stat v =
    "      \"options\": { " ++ reduceInner
      ++ ", \"colorMode\": \"" ++ colorModeName (StatViz.colorMode v) ++ "\""
      ++ ", \"graphMode\": \"" ++ graphModeName (StatViz.graphMode v) ++ "\""
      ++ ", \"textMode\": \""  ++ textModeName  (StatViz.textMode  v) ++ "\""
      ++ ", \"justifyMode\": \"auto\" }," ++ nl
  optionsField Gauge v =
    "      \"options\": { " ++ reduceInner
      ++ ", \"showThresholdMarkers\": " ++ showBool (GaugeViz.showThresholdMarkers v)
      ++ " }," ++ nl
  optionsField BarGauge v =
    "      \"options\": { " ++ reduceInner
      ++ ", \"displayMode\": \"" ++ barDisplayName (BarGaugeViz.display v) ++ "\""
      ++ ", \"showUnfilled\": true }," ++ nl

  -- fieldConfig.defaults.custom: solo TimeSeries ha custom field config.
  customDefaults : (k : PanelKind) → Viz k → String
  customDefaults TimeSeries v =
    "\"custom\": { \"drawStyle\": \"line\", \"showPoints\": \"never\""
      ++ ", \"lineWidth\": "      ++ showℕ (TimeSeriesViz.lineWidth   v)
      ++ ", \"fillOpacity\": "    ++ showℕ (TimeSeriesViz.fillOpacity v)
      ++ ", \"gradientMode\": \"" ++ gradientName (TimeSeriesViz.gradientMode v) ++ "\" }"
  customDefaults Stat          _ = ""
  customDefaults Gauge         _ = ""
  customDefaults BarGauge      _ = ""
  customDefaults Table         _ = ""
  customDefaults StatusHistory _ = ""

  -- Oggetto `datasource` Grafana: `type` sempre, `uid` se presente.
  dsUidField : Maybe String → String
  dsUidField nothing  = ""
  dsUidField (just u) = ", \"uid\": \"" ++ escapeJSON u ++ "\""

  dsJson : Datasource → String
  dsJson ds =
    "{ \"type\": \"" ++ escapeJSON (Datasource.grafanaType ds) ++ "\""
      ++ dsUidField (Datasource.uid ds) ++ " }"

  -- ─── fieldConfig.defaults ─────────────────────────────────────────

  renderSteps : List (Float × String) → String
  renderSteps []             = ""
  renderSteps ((v , c) ∷ ss) =
    ", { \"color\": \"" ++ escapeJSON c
      ++ "\", \"value\": " ++ showFloat v ++ " }"
      ++ renderSteps ss

  renderThresholds : Thresholds → String
  renderThresholds th =
    "{ \"mode\": \"absolute\", \"steps\": [ { \"color\": \""
      ++ escapeJSON (Thresholds.baseColor th) ++ "\", \"value\": null }"
      ++ renderSteps (Thresholds.steps th)
      ++ " ] }"

  -- Pezzi opzionali dei defaults: unit, (color+thresholds), custom.
  -- Si concatenano solo quelli presenti, separati da virgola.
  nonempties : List String → List String
  nonempties []       = []
  nonempties (s ∷ ss) with does (s ≟ˢ "")
  ... | true  = nonempties ss
  ... | false = s ∷ nonempties ss

  joinComma : List String → String
  joinComma []           = ""
  joinComma (s ∷ [])     = s
  joinComma (s ∷ t ∷ ts) = s ++ ", " ++ joinComma (t ∷ ts)

  unitPiece : FieldConfig → String
  unitPiece fc =
    maybe (λ u → "\"unit\": \"" ++ escapeJSON u ++ "\"") "" (FieldConfig.unit fc)

  -- Con soglie attive serve anche `color.mode = thresholds`, altrimenti
  -- timeseries (e lo sfondo delle stat) le ignorano.
  thrPiece : FieldConfig → String
  thrPiece fc =
    maybe (λ th → "\"color\": { \"mode\": \"thresholds\" }, \"thresholds\": "
                    ++ renderThresholds th)
          "" (FieldConfig.thresholds fc)

  renderFieldConfig : (k : PanelKind) → Viz k → FieldConfig → String
  renderFieldConfig k v fc =
    "{ \"defaults\": { "
      ++ joinComma (nonempties (unitPiece fc ∷ thrPiece fc ∷ customDefaults k v ∷ []))
      ++ " }, \"overrides\": [] }"

  -- Render di un singolo target; `instS` (la stringa instant) è comune a
  -- tutti i target del panel, calcolata una volta dal viz.
  renderOneTarget : (ds : Datasource) (k : PanelKind)
                  → String → ℕ → Target ds k → String
  renderOneTarget ds k instS n t =
    "{ \"refId\": \"" ++ refIdOf n ++ "\""
      ++ ", \"expr\": \""
        ++ escapeJSON (Datasource.render ds (Target.query t)) ++ "\""
      ++ aliasField (Target.alias t)
      ++ instS
      ++ ", \"hide\": " ++ showBool (Target.hidden t)
      ++ " }"

  -- Tail di una `List` di Target con indice corrente.
  renderTargetsTail : (ds : Datasource) (k : PanelKind)
                    → String → ℕ → List (Target ds k) → String
  renderTargetsTail _  _ _     _ []       = ""
  renderTargetsTail ds k instS n (t ∷ ts) =
    ", " ++ renderOneTarget ds k instS n t
         ++ renderTargetsTail ds k instS (suc n) ts

  -- Array `targets` per un panel: lista non vuota, refId derivato.
  renderTargets : (ds : Datasource) (k : PanelKind)
                → String → List⁺ (Target ds k) → String
  renderTargets ds k instS ts =
    "[" ++ renderOneTarget    ds k instS 0 (head ts)
        ++ renderTargetsTail  ds k instS 1 (tail ts)
        ++ "]"

  renderPanel : Rect → AnyPanel → String
  renderPanel pos ap =
    let ds    = AnyPanel.ds ap
        k     = AnyPanel.kind ap
        p     = AnyPanel.panel ap
        vz    = Panel.viz p
        instS = instantField (instantViz k vz) in
    "    {"                                                                ++ nl ++
    "      \"type\": \"" ++ panelTypeOf k ++ "\","                          ++ nl ++
    "      \"title\": \"" ++ escapeJSON (Panel.title p) ++ "\","            ++ nl ++
    "      \"datasource\": " ++ dsJson ds ++ ","                            ++ nl ++
    "      \"fieldConfig\": " ++ renderFieldConfig k vz (Panel.config p) ++ "," ++ nl ++
    optionsField k vz ++
    "      \"gridPos\": { \"x\": " ++ showℕ (x pos)
                     ++ ", \"y\": " ++ showℕ (y pos)
                     ++ ", \"w\": " ++ showℕ (w pos)
                     ++ ", \"h\": " ++ showℕ (h pos) ++ " },"               ++ nl ++
    "      \"targets\": " ++ renderTargets ds k instS (Panel.targets p)     ++ nl ++
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
    "{ \"text\": \"" ++ escapeJSON v
      ++ "\", \"value\": \"" ++ escapeJSON v ++ "\" }"

  renderVarOptionsTail : List String → String
  renderVarOptionsTail []       = ""
  renderVarOptionsTail (v ∷ vs) =
    ", " ++ renderVarOption v ++ renderVarOptionsTail vs

  renderVarOptions : List⁺ String → String
  renderVarOptions opts =
    "[" ++ renderVarOption     (head opts)
        ++ renderVarOptionsTail (tail opts)
        ++ "]"

  varQueryString : List⁺ String → String
  varQueryString opts = go (head opts) (tail opts)
    where
      go : String → List String → String
      go h []       = h
      go h (v ∷ vs) = h ++ "," ++ go v vs

  -- Query `label_values` per variabili Prometheus.
  labelValuesQuery : Maybe String → String → String
  labelValuesQuery nothing  l = "label_values(" ++ l ++ ")"
  labelValuesQuery (just m) l = "label_values(" ++ m ++ ", " ++ l ++ ")"

  -- Con includeAll la selezione di default è "All" (`$__all`) e le
  -- opzioni la includono in testa, come nel JSON che Grafana esporta.
  allOption : String
  allOption = "{ \"selected\": true, \"text\": \"All\", \"value\": \"$__all\" }"

  customCurrent : Bool → List⁺ String → String
  customCurrent true  _    = "{ \"text\": \"All\", \"value\": \"$__all\" }"
  customCurrent false opts = renderVarOption (head opts)

  customOptions : Bool → List⁺ String → String
  customOptions false opts = renderVarOptions opts
  customOptions true  opts =
    "[" ++ allOption ++ ", " ++ renderVarOption (head opts)
        ++ renderVarOptionsTail (tail opts)
        ++ "]"

  -- `refresh: 2` = on time range change: senza, Grafana non popola mai
  -- le opzioni di una query variable importata. Niente `allValue`: con
  -- includeAll Grafana interpola l'alternanza di tutti i valori, che
  -- con il matcher `=~` resta fedele.
  renderVariable : Variable → String
  renderVariable v with Variable.spec v
  ... | customSpec opts multi inc =
        "{ \"name\": \"" ++ escapeJSON (Variable.name v) ++ "\""   ++
        ", \"type\": \"custom\""                                   ++
        ", \"query\": \"" ++ escapeJSON (varQueryString opts) ++ "\"" ++
        ", \"multi\": " ++ showBool multi                          ++
        ", \"includeAll\": " ++ showBool inc                       ++
        ", \"current\": " ++ customCurrent inc opts                ++
        ", \"options\": " ++ customOptions inc opts                ++
        " }"
  ... | querySpec src fld multi inc =
        "{ \"name\": \"" ++ escapeJSON (Variable.name v) ++ "\""   ++
        ", \"type\": \"query\""                                    ++
        ", \"datasource\": { \"type\": \"" ++ escapeJSON src ++ "\" }" ++
        ", \"query\": { \"find\": \"terms\", \"field\": \"" ++ escapeJSON fld ++ "\" }" ++
        ", \"refresh\": 2"                                         ++
        ", \"multi\": " ++ showBool multi                          ++
        ", \"includeAll\": " ++ showBool inc                       ++
        " }"
  ... | promQuerySpec m lbl multi inc =
        "{ \"name\": \"" ++ escapeJSON (Variable.name v) ++ "\""   ++
        ", \"type\": \"query\""                                    ++
        ", \"datasource\": { \"type\": \"prometheus\" }"           ++
        ", \"query\": \"" ++ escapeJSON (labelValuesQuery m lbl) ++ "\"" ++
        ", \"refresh\": 2"                                         ++
        ", \"multi\": " ++ showBool multi                          ++
        ", \"includeAll\": " ++ showBool inc                       ++
        " }"

  joinVars : List Variable → String
  joinVars []           = ""
  joinVars (v ∷ [])     = renderVariable v
  joinVars (v ∷ w ∷ vs) = renderVariable v ++ ", " ++ joinVars (w ∷ vs)

  renderTemplating : List Variable → String
  renderTemplating vars = "{ \"list\": [" ++ joinVars vars ++ "] }"

-- ─────────────────────────────────────────────────────────────────────
-- Dedup per nome (prima occorrenza vince) sulla concatenazione dei
-- riferimenti raccolti dai panel + extras della dashboard. La raccolta
-- da Tiling vive in Penelope.Dashboard (così la well-formedness della
-- Dashboard può vincolarla a livello di tipo).
-- ─────────────────────────────────────────────────────────────────────

private
  hasName : String → List Variable → Bool
  hasName _ []       = false
  hasName n (v ∷ vs) with does (n ≟ˢ Variable.name v)
  ... | true  = true
  ... | false = hasName n vs

  dedup : List Variable → List Variable
  dedup []       = []
  dedup (v ∷ vs) with hasName (Variable.name v) vs
  ... | true  = dedup vs
  ... | false = v ∷ dedup vs

-- Variabili effettive della dashboard: prima i refs raccolti dai panel,
-- poi gli "extras" di Dashboard.variables (utili per variabili usate
-- solo nei titoli). Dedupplicate per `name`.
dashboardVariables : Dashboard → List Variable
dashboardVariables d =
  dedup (collectPanelVars (Dashboard.tiling d) ++ˡ Dashboard.variables d)

renderDashboard : Dashboard → String
renderDashboard d =
  let panels = walk (Dashboard.tiling d)
      tmpl   = renderTemplating (dashboardVariables d) in
    "{"                                                ++ nl ++
    "  \"title\": \"" ++ escapeJSON (Dashboard.title d) ++ "\"," ++ nl ++
    "  \"uid\": \"" ++ escapeJSON (Dashboard.uid d) ++ "\","     ++ nl ++
    "  \"schemaVersion\": 39,"                          ++ nl ++
    "  \"timezone\": \"browser\","                      ++ nl ++
    "  \"editable\": true,"                             ++ nl ++
    "  \"refresh\": \"30s\","                           ++ nl ++
    "  \"time\": { \"from\": \"now-6h\", \"to\": \"now\" }," ++ nl ++
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
