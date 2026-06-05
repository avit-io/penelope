{-# OPTIONS --safe --without-K #-}

module Penelope.Backend.Loquel where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Loquel backend per Penelope. Loquel è l'astrazione neutra che     ║
-- ║  copre Loki ed Elastic: UNA QueryLang sola, DUE Datasource         ║
-- ║  (`loki s`, `elastic s`). Una stessa query Loquel può essere       ║
-- ║  impacchettata in un panel su `loki s` e in un altro su            ║
-- ║  `elastic s`: il render risultante usa due frammenti distinti      ║
-- ║  (LogQL via Loquel.Render.LogQL vs JSON via Loquel.Render.Elastic).║
-- ║                                                                    ║
-- ║  `faithful?` PER PANEL: ogni datasource usa il proprio frammento   ║
-- ║  fedele (faithfulLogQLB / faithfulElasticB). Una pipe non fedele   ║
-- ║  rifiuta il typecheck nel panel su quel datasource.                ║
-- ║                                                                    ║
-- ║  Il LQKind classifica i tre "ruoli" che una query Loquel ricopre:  ║
-- ║   • scalarM   → Stat/Gauge/BarGauge   (instantanea)                ║
-- ║   • rangeM    → TimeSeries            (con finestra)               ║
-- ║   • logStream → Table                 (log lines)                  ║
-- ║                                                                    ║
-- ║  Il `Ctx` (lo schema Loquel di partenza) compare via Lift perché   ║
-- ║  QueryLang.Ctx è in Set₁ ma Schema vive in Set.                    ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Level                       using (Level; Lift; lift; lower)
open import Data.Bool                   using (Bool; true; false; T; _∧_)
open import Data.Char.Base              using (Char)
open import Data.List.Base              using (List; []; _∷_; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product.Base           using (_,_)
open import Data.String                 using (String; _++_; toList)

open import Loquel.Schema               using (Schema; Ty; TStr; TBool)
open import Loquel.Expr                 using (Expr; var; lit; _≡ᵉ_)
open import Loquel.Pipe                 using (Pipe)
open import Loquel.Render.LogQL         using (renderLogQL; MetricKind;
                                               LogQLWindow; renderMetricLogQL)
open import Loquel.Render.Elastic       using (renderElastic)
open import Loquel.Render.Faithful      using (faithfulLogQLB; faithfulElasticB)
open import Loquel.Render.JSON          using (serialize)

open import Penelope.Panel
open import Penelope.Query
open import Penelope.Datasource
open import Penelope.Variable           using (Variable; mkQueryVariable)

-- I tre ruoli che una query Loquel ricopre in un panel.
data LQKind : Set where
  scalarM   : LQKind
  rangeM    : LQKind
  logStream : LQKind

loquelQueryTypeOf : PanelKind → LQKind
loquelQueryTypeOf Stat          = scalarM
loquelQueryTypeOf Gauge         = scalarM
loquelQueryTypeOf BarGauge      = scalarM
loquelQueryTypeOf TimeSeries    = rangeM
loquelQueryTypeOf StatusHistory = rangeM
loquelQueryTypeOf Table         = logStream

-- Ctx Loquel: lo schema di partenza, lifted in Set₁ per uniformità con
-- QueryLang.Ctx.
CtxL : Set₁
CtxL = Lift _ Schema

-- La query Loquel impacchetta una Pipe (con i suoi schemi esistenziali)
-- più i metadati specifici del ruolo:
--   • scalarM:   Pipe + MetricKind + by-labels.
--   • rangeM:    Pipe + MetricKind + by-labels + finestra.
--   • logStream: Pipe pura.
-- Lo schema di partenza `a` è parametro; il secondo schema `b` resta
-- esistenziale: ad ogni stadio Loquel ne cambia la forma, ma da
-- Penelope non lo guardiamo.
data LoquelTarget' (a : Schema) : LQKind → Set where
  scalarT : ∀ {b} → Pipe a b → MetricKind → List String
          → LoquelTarget' a scalarM
  rangeT  : ∀ {b} → Pipe a b → MetricKind → List String → LogQLWindow
          → LoquelTarget' a rangeM
  logT    : ∀ {b} → Pipe a b
          → LoquelTarget' a logStream

-- Surface a livello CtxL: scarta il Lift per riallinearsi a Schema.
-- Resta a Set perché LoquelTarget' lo è.
LoquelTarget : CtxL → LQKind → Set
LoquelTarget c τ = LoquelTarget' (lower c) τ

Loquel : QueryLang
Loquel = record
  { Ctx         = CtxL
  ; QueryType   = LQKind
  ; Query       = LoquelTarget
  ; queryTypeOf = loquelQueryTypeOf
  }

-- ─── Loki datasource ────────────────────────────────────────────────

renderLoki : ∀ {c τ} → LoquelTarget c τ → String
renderLoki (logT p)              = renderLogQL p
renderLoki (rangeT  p k by w)    = renderMetricLogQL p k by w
renderLoki (scalarT p k by)      = renderMetricLogQL p k by "1m"

faithfulLoki?B : ∀ {c τ} → LoquelTarget c τ → Bool
faithfulLoki?B (logT p)              = faithfulLogQLB p
faithfulLoki?B (rangeT  p _ _ _)     = faithfulLogQLB p
faithfulLoki?B (scalarT p _ _)       = faithfulLogQLB p

loki : Schema → Datasource
loki s = record
  { lang        = Loquel
  ; ctx         = lift s
  ; grafanaType = "loki"
  ; render      = renderLoki
  ; faithful?   = faithfulLoki?B
  }

-- ─── Elastic datasource ─────────────────────────────────────────────

renderElasticS : ∀ {c τ} → LoquelTarget c τ → String
renderElasticS (logT p)          = serialize (renderElastic p)
renderElasticS (rangeT  p _ _ _) = serialize (renderElastic p)
renderElasticS (scalarT p _ _)   = serialize (renderElastic p)

faithfulElastic?B : ∀ {c τ} → LoquelTarget c τ → Bool
faithfulElastic?B (logT p)          = faithfulElasticB p
faithfulElastic?B (rangeT  p _ _ _) = faithfulElasticB p
faithfulElastic?B (scalarT p _ _)   = faithfulElasticB p

elastic : Schema → Datasource
elastic s = record
  { lang        = Loquel
  ; ctx         = lift s
  ; grafanaType = "elasticsearch"
  ; render      = renderElasticS
  ; faithful?   = faithfulElastic?B
  }

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Variabili di dashboard ANCORATE allo schema Loquel.               ║
-- ║                                                                    ║
-- ║  `Var s` è la dichiarazione TIPATA di una variabile: porta con sé  ║
-- ║  la prova che il campo `fieldName` esiste in `s` e che è un campo  ║
-- ║  esatto (suffisso ".keyword"). Una variabile su un campo           ║
-- ║  inesistente (Test negativo 1) o su un campo di testo libero      ║
-- ║  (Test negativo 2) non typeckecka.                                 ║
-- ║                                                                    ║
-- ║  Il combinatore `_==ᵛ_` produce un filtro Loquel `var f ≡ᵉ lit     ║
-- ║  "$name"`: per render/faithful? è un'uguaglianza esatta su campo   ║
-- ║  TStr, quindi NEL FRAMMENTO FEDELE. Per Grafana è un sentinella    ║
-- ║  che verrà sostituito a view-time.                                 ║
-- ║                                                                    ║
-- ║  POLICY analizzato→esatto: l'utente deve referenziare il campo     ║
-- ║  `.keyword` (es. "LoggerLevel.keyword") perché è quello su cui     ║
-- ║  l'uguaglianza esatta resta fedele in Elastic. I campi senza       ║
-- ║  suffisso ".keyword" sono trattati come testo libero e rifiutati.  ║
-- ╚════════════════════════════════════════════════════════════════════╝

-- Predicato decidibile "questa stringa termina in `.keyword`".
-- Implementato via reverse + pattern match sui chars del suffisso
-- "drowyek.", così riduce definizionalmente sui literal di stringa.
private
  endsKeyword-rev : List Char → Bool
  endsKeyword-rev ('d' ∷ 'r' ∷ 'o' ∷ 'w' ∷ 'y' ∷ 'e' ∷ 'k' ∷ '.' ∷ _) = true
  endsKeyword-rev _                                                    = false

endsKeyword : String → Bool
endsKeyword s = endsKeyword-rev (reverse (toList s))

-- La variabile tipata: dichiarata su uno schema `s`, ancora una prova
-- di esistenza del campo (`fieldProof`) e una prova che il campo è un
-- `.keyword` (la prova è implicita e si risolve a `tt` quando il check
-- riduce a `true`).
record Var (s : Schema) : Set where
  constructor mkVar′
  field
    name       : String
    fieldName  : String
    fieldProof : (fieldName , TStr) ∈ s
    keywordOK  : T (endsKeyword fieldName)
    multi      : Bool
    includeAll : Bool

-- Smart constructor: la prova `keywordOK` è implicita. Sui literal di
-- stringa con suffisso ".keyword" il check riduce a `true`, l'utente
-- non passa nulla. Su literal senza ".keyword" il check è `false` e il
-- typecheck fallisce (Test negativo 2).
mkVar : ∀ {s} (name fieldName : String)
        (fieldProof : (fieldName , TStr) ∈ s)
        (multi includeAll : Bool)
        {keywordOK : T (endsKeyword fieldName)} → Var s
mkVar n f p m a {kw} = mkVar′ n f p kw m a

-- Iniezione nella forma opaca usata dal renderer JSON. Lo
-- `sourceGrafanaType` viene timbrato esplicitamente dal sito chiamante
-- (un datasource Loquel può essere loki o elastic). Helper specifici:
varToVariable : ∀ {s} → (sourceGrafanaType : String) → Var s → Variable
varToVariable src v = mkQueryVariable (Var.name v) src (Var.fieldName v)
                                       (Var.multi v) (Var.includeAll v)

elasticVar : ∀ {s} → Var s → Variable
elasticVar = varToVariable "elasticsearch"

lokiVar : ∀ {s} → Var s → Variable
lokiVar = varToVariable "loki"

-- Combinatore: `p ==ᵛ v` è il filtro `var p ≡ᵉ lit "$name"`.
-- Il campo della prova `p` e quello dichiarato in `v` non sono forzati
-- a coincidere dal tipo (sarebbe rumoroso): la coerenza è discipline
-- dell'utente. Le clausole di registrazione passano per `Panel.vars`.
infix 4 _==ᵛ_
_==ᵛ_ : ∀ {s f} → (f , TStr) ∈ s → Var s → Expr s TBool
p ==ᵛ v = var p ≡ᵉ lit ("$" ++ Var.name v)

