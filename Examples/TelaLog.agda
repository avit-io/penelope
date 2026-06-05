{-# OPTIONS --safe --without-K #-}

module Examples.TelaLog where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Una query, due render.                                            ║
-- ║                                                                    ║
-- ║  Il *frammento Loquel fedele* sia per LogQL che per Elastic        ║
-- ║  contiene `filterp (var f ≡ᵉ lit v)` su campi TStr (label/term).   ║
-- ║  Quindi la stessa pipe `q` è renderizzabile fedelmente in entrambi:║
-- ║   • via `loki s`    → LogQL  `{app="webapp"}`                      ║
-- ║   • via `elastic s` → Elastic JSON `{"term":{"app":"webapp"}}`     ║
-- ║                                                                    ║
-- ║  Il `target` dei due panel è LO STESSO `logT q` (refl); il render  ║
-- ║  che esce è diverso, perché il datasource determina la stringa     ║
-- ║  emessa. È esattamente "il datasource è per-panel".                ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Loquel.Schema       using (Schema; TStr)
open import Loquel.Expr         using (var; lit; _≡ᵉ_)
open import Loquel.Pipe         using (Pipe; filterp)

open import Data.List.Membership.Propositional        using (_∈_)
open import Data.List.Relation.Unary.Any              using (here; there)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Data.Unit                                  using (tt)
open import Data.Product                               using (_,_)

open import Penelope.Panel
open import Penelope.Datasource
open import Penelope.Backend.Loquel
open import Penelope.Tiling
open import Penelope.Dashboard
open import Penelope.JSON
open import Penelope.Sugar

open import Data.String using (String)
open import Data.List   using (_∷_; [])

-- ── Schema ────────────────────────────────────────────────────────────
logSchema : Schema
logSchema = ("app" , TStr) ∷ []

app∈ : ("app" , TStr) ∈ logSchema
app∈ = here refl

-- ── UNA sola query Loquel ─────────────────────────────────────────────
q : Pipe logSchema logSchema
q = filterp (var app∈ ≡ᵉ lit "webapp")

-- ── DUE datasource che condividono la stessa QueryLang (Loquel) ──────
lokiDS    : Datasource
lokiDS    = loki    logSchema

elasticDS : Datasource
elasticDS = elastic logSchema

-- ── DUE panel con la STESSA target ────────────────────────────────────
panelL : Panel lokiDS Table
panelL = record { title = "via Loki"    ; target = logT q ; ok = tt }

panelE : Panel elasticDS Table
panelE = record { title = "via Elastic" ; target = logT q ; ok = tt }

-- Refl: i target dei due panel sono la stessa cosa (entrambi `logT q`,
-- entrambi di tipo `LoquelTarget' logSchema logStream`).
sameTarget : Panel.target panelL ≡ Panel.target panelE
sameTarget = refl

-- ── Due render distinti, dalla stessa target. ─────────────────────────
renderL : String
renderL = Datasource.render lokiDS    (Panel.target panelL)

renderE : String
renderE = Datasource.render elasticDS (Panel.target panelE)

-- Golden — fissati per refl, così se cambiano i renderer il modulo
-- non typeckecka.
_ : renderL ≡ "{app=\"webapp\"}"
_ = refl

_ : renderE ≡ "{\"query\":{\"term\":{\"app\":\"webapp\"}}}"
_ = refl

-- ── La tela: 12×8 ↔ 12×8 → 24×8 ───────────────────────────────────────
viewport : Rect
viewport = mkRect 0 0 24 8

tela : TilingOf AnyPanel viewport
tela = left ↔ right
  where
    left  : Tiling AnyPanel 0 0 12 8
    left  = tile (□ panelL)
    right : Tiling AnyPanel 12 0 12 8
    right = tile (□ panelE)

unaQueryDueRender : Dashboard
unaQueryDueRender =
  mkDashboard "Una query, due render" "una-due-render"
              [] viewport tela

json : String
json = renderDashboard unaQueryDueRender

-- ── Test negativo (documentato) ─────────────────────────────────────────
--
-- Una pipe che proietta tramite `parse` su un campo diverso da "line"
-- NON sta nel frammento fedele di LogQL, quindi non può essere il
-- target di un panel su `lokiDS`:
--
--   open import Loquel.Pipe using (parse)
--   ...
--   noFaithful : Pipe logSchema (...)
--   noFaithful = parse (var app∈) ...        -- WF su un campo non-line
--
--   bad : Panel lokiDS Table
--   bad = record { title = "no"
--                ; target = logT noFaithful
--                ; ok = tt }
--   -- ✗ tt ha tipo ⊤, ma il campo `ok` chiede T false ≡ ⊥
