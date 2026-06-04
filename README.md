# Penelope

<p align="center">
  <img src="logo.svg" width="160" alt="Penelope — il telaio con la tela tessuta di τ, ℳ, ⊢, Σ"/>
</p>

> *Tesse e disfa la tela delle tue metriche — ma il telaio è tipato.*

Verifiable Grafana dashboards in Agda — geometria (slicing floorplan) e decorazione (panel Grafana) separate, integrazione nativa con HenQL.

---

## Il problema

Una dashboard Grafana è un file JSON di parecchie centinaia di righe. Ogni
panel ha un `type` (`timeseries`, `stat`, `gauge`, `table`) e una lista di
`targets` con espressioni PromQL. **Niente garantisce che il tipo del panel
sia compatibile con il tipo della query**: un panel `stat` con una
`rate(...)[5m]` come target è un errore silenzioso, scoperto solo quando
Grafana mostra il vuoto.

E la disposizione? `gridPos` è un quartetto `(x, y, w, h)` libero. Due
panel possono sovrapporsi, scappare dal canvas, lasciare buchi. Tutto JSON
sintatticamente valido, tutto rotto a livello visivo.

---

## Come funziona

Penelope codifica entrambi i vincoli **nella struttura dei tipi**. Nessuna
prova `.proof` attaccata: le regole sono nello shape.

### Il panel kind determina il PromType — non lo *vincola*, lo *è*

```agda
data PanelKind : Set where
  TimeSeries Stat Gauge Table : PanelKind

queryTypeOf : PanelKind → PromType
queryTypeOf TimeSeries = InstantVector
queryTypeOf Stat       = Scalar
queryTypeOf Gauge      = Scalar
queryTypeOf Table      = InstantVector

record Panel (M : Model) (k : PanelKind) : Set where
  field
    title   : String
    targets : List⁺ (Expr M (queryTypeOf k))
```

Non c'è un campo `.proof : queryTypeOf k ≡ τ`. Il tipo delle `targets` è
**già** `List⁺ (Expr M (queryTypeOf k))`. Mettere un `Expr M Scalar` in
un panel `TimeSeries` non è un errore di validazione runtime: è un
errore di unificazione del typechecker. Tutte le target di un panel
condividono lo stesso PromType (overlay di metriche compatibili). La
spec è nello shape, non nei commenti.

### Due livelli: geometria intrinseca, decorazione separata

**Livello geometrico** (`Penelope.Tiling`) — completamente indipendente
da Grafana. Un tassellamento è indicizzato sul rettangolo che tassella:

```agda
data Tiling : (x y w h : ℕ) → Set where
  tile : ∀ {x y w h} → Tiling x y w h
  hcut : ∀ {x y w} {ht hb : ℕ}
       → Tiling x y w (suc ht)
       → Tiling x (y + suc ht) w (suc hb)
       → Tiling x y w (suc ht + suc hb)
  vcut : ∀ {x y h} {wl wr : ℕ}
       → Tiling x y (suc wl) h
       → Tiling (x + suc wl) y (suc wr) h
       → Tiling x y (suc wl + suc wr) h
```

Le sotto-dimensioni dei figli sono `suc`-indicizzate, quindi **min-size
≥ 1 è definizionale**: nessuna cella può avere `w = 0` o `h = 0`. I
rettangoli figli sono *calcolati dagli indici*, non scelti a parte.

**Classe coperta**: i tassellamenti rappresentabili sono gli **slicing
floorplan** (partizioni guillotine) — partizioni del rettangolo per
tagli completi orizzontali o verticali ricorsivi. Il pinwheel a 5
rettangoli e altri tassellamenti non-guillotine **non sono esprimibili**.
È una limitazione strutturale, non un buco di copertura.

I lemmi geometrici sono dimostrati **una volta** nel modulo `Tiling`:

```agda
contained : (t : Tiling x y w h) (l : Leaf t) → place t l ⊆ mkRect x y w h
disjoint  : (t : Tiling x y w h) (l₁ l₂ : Leaf t)
          → l₁ ≢ l₂ → Disjoint (place t l₁) (place t l₂)
```

**Livello decorazione** (`Penelope.Dashboard`) — etichetta le foglie del
tassellamento con panel. Container style: shape + payload:

```agda
record Dashboard (M : Model) : Set where
  field
    viewport : Rect
    tiling   : TilingOf viewport
    label    : Leaf tiling → AnyPanel M
```

La decorazione **non tocca** la geometria. Cambiare il tassellamento
non richiede toccare le query; cambiare i panel non richiede ridimostrare
la disgiunzione. I due assi sono ortogonali.

Il renderer deriva i `gridPos` da `place` del tassellamento — non più
da un walk ad albero conflato. È totale e i `gridPos` emessi sono validi
**per costruzione** (nessun `h = 0` possibile):

```agda
renderDashboard : {M : Model} → Dashboard M → String
```

---

## La metafora

Penelope, moglie di Ulisse, **tesse di giorno la tela funebre per Laerte
e la disfa di notte** — per ingannare i pretendenti fino al ritorno del
marito. Le metriche funzionano allo stesso modo: una dashboard non è mai
*finita*, si riscrive ogni volta che il sistema cambia, si rifà ogni volta
che ti serve guardare qualcos'altro. Penelope non si lamenta del
rifacimento — **lo verifica**. Ogni rifacimento è una nuova tela tessuta,
e il telaio (il typechecker) garantisce che ogni filo abbia il tipo
giusto prima ancora che la tela esca dal subbio.

| Penelope             | Grafana / Agda                                       |
|----------------------|------------------------------------------------------|
| la tela              | `Tiling x y w h`, il tassellamento guillotine        |
| il filo              | un singolo `Panel M k`                               |
| il telaio            | il typechecker Agda                                  |
| `tile`               | una cella foglia                                     |
| `hcut`               | taglio orizzontale: top sopra bottom                 |
| `vcut`               | taglio verticale: left accanto a right               |
| `label`              | la decorazione: a ogni foglia il suo panel           |
| `queryTypeOf k`      | il tipo del filo imposto dal panel kind              |
| il pretendente       | una query non tipata che entrerebbe a runtime        |
| disfare la tela      | ri-editare il modulo, ri-typeckeckare                |
| Ulisse che torna     | il deploy di Grafana — la tela esce dal telaio       |

> *Una dashboard senza tipi è una tela che Penelope, al risveglio, non
> riconoscerebbe più.*

---

## Come libreria

```nix
# flake.nix del tuo progetto
inputs.penelope.url = "github:avit-io/penelope";
inputs.penelope.inputs.nixpkgs.follows = "nixpkgs";
inputs.penelope.inputs.piforge.follows = "piforge";

devShells.x86_64-linux.default =
  inputs.penelope.lib.mkShell {
    pkgs = nixpkgs.legacyPackages.x86_64-linux;
  };
```

```
# mio-progetto.agda-lib
name: mio-progetto
include: .
depend: standard-library prometea henql penelope
```

```agda
open import Prometea.Core
open import HenQL.Syntax
open import Penelope.Panel
open import Penelope.Tiling
open import Penelope.Dashboard
open import Penelope.JSON
open import Penelope.Sugar     -- timeseries/stat/... · □_ · ↕/↔

miaApp : Model
miaApp = record { Time = ℕ ; Val = Float ; Series = String }

errori : Panel miaApp TimeSeries
errori = timeseries "Errori / s"
  (sumBy ("job" ∷ []) (rate (range "http_requests_errors_total" 5)))

latenza : Panel miaApp TimeSeries
latenza = timeseries "Latenza"
  (rate (range "http_request_duration_seconds_sum" 5))

budget : Panel miaApp Stat
budget = stat "Budget consumato" (scalar "0.42")

-- Geometria: tassellamento del viewport 24×16, con infix ↕/↔.
viewport : Rect
viewport = mkRect 0 0 24 16

tela : TilingOf viewport
tela = (left ↔ right) ↕ bot
  where
    left  : Tiling 0 0 12 8
    left  = tile
    right : Tiling 12 0 12 8
    right = tile
    bot   : Tiling 0 8 24 8
    bot   = tile

-- Decorazione: ogni foglia → un panel, kind recuperato dal tipo via □_.
decora : Leaf tela → AnyPanel miaApp
decora (topL (leftL here))  = □ errori
decora (topL (rightL here)) = □ latenza
decora (botL here)          = □ budget

salute : Dashboard miaApp
salute = mkDashboard "Salute API" "salute-api" [] viewport tela decora
--                                              ↑
--                                   nessuna template variable

-- renderDashboard salute : String — Grafana JSON pronto.
```

### Template variables

`Variable` rappresenta un placeholder che Grafana sostituisce a runtime
nelle query (tipologia MVP: `custom`, lista esplicita di valori). Si
referenzia in PromQL con `varRef`:

```agda
serviceVar : Variable
serviceVar = mkVariable "service"
  ("frontend" ∷ "backend" ∷ "api" ∷ [])

errori : Panel miaApp TimeSeries
errori = timeseries "Errori / s"
  (rate (range
    ("http_requests_errors_total{service=\"" ++ varRef serviceVar ++ "\"}")
    5))

salute = mkDashboard "Salute API" "salute-api"
                     (serviceVar ∷ [])    -- ← registrata nelle variables
                     viewport tela decora
```

Il renderer emette il blocco `templating.list` nel JSON; Grafana mostra
il selettore in alto alla dashboard e sostituisce `$service` con il
valore scelto prima dell'invio della query a Prometheus.

Il binder `forEach` lega la variabile localmente, utile quando i panel
sono definiti inline e devono catturare la variabile:

```agda
salute = forEach "service" ("frontend" ∷ "backend" ∷ []) λ service →
  mkDashboard "Salute API" "salute-api" [] viewport tela (decora-of service)
  where
    decora-of : Variable → Leaf tela → AnyPanel miaApp
    decora-of v (topL (leftL here))  = □ (errori-of v)
    -- ...
    errori-of : Variable → Panel miaApp TimeSeries
    errori-of v = timeseries "Errori / s"
      (rate (range ("http_requests_errors_total{service=\"" ++ varRef v ++ "\"}") 5))
```

`forEach` pre-pende la variabile alla lista; più `forEach` in cascata
le accumulano nella stessa dashboard.

> Lo zucchero in `Penelope.Sugar` è interamente fatto di definizioni
> sull'algebra esistente (riducono a `mkPanel`, `hcut`, `vcut`, `Σ._,_`).
> Nessun nuovo data type, nessuna prova ulteriore: gli invarianti di
> `Tiling` e `Panel` sono ereditati. Se volessi controllo fine, puoi
> ignorare `Sugar` e scrivere `mkPanel`/`hcut`/`vcut` direttamente.

### Come sviluppatore di Penelope

```bash
git clone https://github.com/avit-io/penelope
cd penelope
nix develop                # Agda 2.8 + stdlib 2.3 + prometea + henql in scope
agda Penelope/JSON.agda    # typecheck completo
agda Examples/Tela.agda    # typecheck dell'esempio
```

---

## Struttura del progetto

```
penelope/
├── Penelope/
│   ├── Tiling.agda      # GEOMETRIA — Rect · Tiling · Leaf · place ·
│   │                    #   contained · disjoint (indipendente da Grafana)
│   ├── Panel.agda       # PanelKind · queryTypeOf · Panel · AnyPanel
│   ├── Variable.agda    # Variable · varRef (template variables custom)
│   ├── Dashboard.agda   # DECORAZIONE — variables + viewport + tiling + label
│   ├── JSON.agda        # renderDashboard — totale, gridPos da place,
│   │                    #   templating.list emesso dalle variables
│   └── Sugar.agda       # ZUCCHERO — □_ · timeseries/stat/... · ↕/↔ · forEach
├── Examples/
│   └── Tela.agda        # esempio: tre panel, tassellamento, render JSON
├── penelope.agda-lib    # depend: standard-library prometea henql
└── flake.nix            # packages.lib · lib.mkShell · devShells.default
```

Il flake espone:

| Output | Contenuto |
|---|---|
| `packages.lib` | la libreria Agda come derivazione Nix |
| `packages.default` | stesso di `lib` |
| `lib.mkShell` | devShell consumer con stdlib + prometea + henql + penelope |
| `devShells.default` | devShell per sviluppare Penelope stessa |

---

## Relazione con l'ecosistema

```
Prometea.Core          ← Model · PromType · Denote
     │
     │  open import Prometea.Core
     ▼
HenQL.Syntax           ← data Expr (M : Model) : PromType → Set
HenQL.Print            ← prettyExpr : Expr M τ → String
     │
     │  open import HenQL.Syntax / HenQL.Print
     ▼
Penelope.Tiling        ← Rect · Tiling · Leaf · place · ⊆ · Disjoint
                         (livello geometrico, zero import Grafana)
Penelope.Panel         ← PanelKind · Panel M k · AnyPanel M
Penelope.Variable      ← Variable · varRef (template variables custom)
Penelope.Dashboard     ← Dashboard M (variables + viewport + tiling + label)
Penelope.JSON          ← renderDashboard → Grafana JSON (con templating)
Penelope.Sugar         ← □_ · timeseries/stat/gauge/table · ↕/↔ · forEach
                         (zucchero, riduce ai costruttori esistenti)
```

Penelope dipende da HenQL per le query e da Prometea per `Model`. Non sa
nulla di Agdovana — sono progetti sorella che consumano gli stessi tipi
fondazionali per fini diversi (Agdovana → regole di alerting,
Penelope → dashboard).

---

## Garanzie strutturali

Cinque invarianti, **nessuna prova attaccata, nessun runtime check**.

- **Coerenza panel ↔ query** — `queryTypeOf k` è computato dal kind. Il
  campo `target : Expr M (queryTypeOf k)` non ammette altri tipi.
  Sostituire un `TimeSeries` con `Stat` cambia il tipo richiesto della
  target; il typechecker rifiuta il sito di costruzione.
- **Min-size definizionale** — i cut di `Tiling` hanno sotto-dimensioni
  `suc`-indicizzate. Una cella di altezza 0 o larghezza 0 non è
  rappresentabile. Nessun `h = 0` può finire nel `gridPos` emesso.
- **Foglie disgiunte** — dimostrato come lemma `disjoint` nel modulo
  `Tiling`. Due foglie distinte di un tassellamento occupano sempre
  rettangoli `Disjoint`. La prova segue per induzione strutturale sul
  Tiling e si chiude con `≤-refl` ai confini dei tagli.
- **Foglie contenute nel viewport** — dimostrato come lemma `contained`.
  Ogni foglia piazzata è `⊆` il rettangolo del Tiling.
- **Coerenza del modello** — `Dashboard M` ha un solo `M`. Tutti i panel
  condividono lo stesso modello semantico (`AnyPanel M = Σ PanelKind
  (Panel M)`). Non puoi mescolare panel di modelli diversi.

`renderDashboard : Dashboard M → String` è **totale**. Nessun caso
parziale, nessuna eccezione runtime. La tela tessuta è sempre JSON
sintatticamente valido, con `gridPos` validi per costruzione.

Per i consumer che vogliono ragionare sull'output:

```agda
renderDashboardCertified
  : (d : Dashboard M)
  → String
  × Σ (List Rect) (λ rs → All (_⊆ viewport d) rs × Pairwise Disjoint rs)
```

restituisce, insieme al JSON, la lista dei `Rect` piazzati con due
prove list-level: tutti contenuti nel viewport (`All ⊆`), pairwise
disgiunti (`Pairwise Disjoint`). Le prove sono derivate dai lemmi
geometrici di `Tiling`, non da una verifica a runtime.

### Cosa NON è garantito

- **Tassellamenti non-guillotine** — Penelope copre gli slicing floorplan.
  Il pinwheel a 5 rettangoli, le partizioni a T-shape e altri layout
  che richiedono un taglio non-completo non sono esprimibili. È una
  scelta di scope: la classe coperta è chiusa, semplice da ragionare,
  e copre il 99% dei layout Grafana realmente usati.
- **Viewport non vuoto** — `tile` accetta `Tiling x y 0 0`. Se passi un
  viewport con `w = 0` o `h = 0`, il rendering emette un canvas vuoto.
  Convenzione consumer-side; nessun cost-of-living per la libreria.

---

## Roadmap

In ordine di valore concreto:

1. **Template variables — tipologie oltre `custom`** — oggi `Variable`
   espone solo la tipologia Grafana `custom` (lista esplicita di valori).
   Da aggiungere: `query` (label_values via PromQL), `interval` (durate),
   `constant`, `text`, `datasource`. Implementabili come somma sui
   `VarSpec` senza toccare il render del blocco `templating`.
2. **Datasource non-Prometheus** — Penelope oggi assume `prometheus`.
   Astrarre `Datasource` parallelo a `Model` per Loki, Tempo, ecc.
3. **Layout proof come API standard** — oggi `renderDashboardCertified`
   espone `Σ (List Rect) (All ⊆ × Pairwise Disjoint)` come ritorno
   esplicito. La prossima iterazione è promuovere quella variante a
   `renderDashboard` di default e deprecare la versione non-certificata.

### Già implementati come derivazioni geometriche

- **`vstack` / `hstack` n-ari** — fold di `hcut` / `vcut` su una pila
  tipata di sotto-Tilings. Disgiuntezza ereditata: il Tiling risultante
  è un BSP regolare, i lemmi `disjoint` e `contained` si applicano senza
  prove ulteriori.
- **Split pesati** — già esprimibili nei costruttori base scegliendo
  `(ht hb)` con la proporzione desiderata. Es. `hcut {ht = 9} {hb = 5}`
  per ~63% / 37% su altezza 16. Le proporzioni vivono nello shape.
- **Zucchero in `Penelope.Sugar`** — `□_`, costruttori per-kind
  (`timeseries`/`stat`/`gauge`/`table`), e infissi `↕`/`↔` come alias di
  `hcut`/`vcut`. Tutto fatto di definizioni sull'algebra: nessun nuovo
  data type, invarianti ereditati. Il single-expression senza
  annotazioni *non* funziona — l'unificatore di Agda non inverte
  `suc n + suc n ≡ 16` per `n` libero — quindi i bracci dei cut hanno
  bisogno di tipi annotati (`where`-clauses). Il livello `Sugar`
  function-based su un viewport (per il sogno "stile old Layout M")
  e i combinatori n-ari `rows` / `cols` per la decomposizione equa
  vivono in roadmap.
- **Template variables (custom MVP)** — `Variable` con `name` e
  `options : List⁺ String`, registrata in `Dashboard.variables`, emessa
  nel blocco `templating.list`. `varRef` produce `$varname` da iniettare
  nelle stringhe PromQL. Binder `forEach` per legare la variabile nel
  corpo della dashboard. Le tipologie Grafana oltre `custom` (`query`,
  `interval`, `constant`, `text`, `datasource`) restano in roadmap.

---

## Contribuire

Se trovi una proprietà delle dashboard Grafana che non è strutturalmente
garantita, apri una issue con il titolo: *"Penelope deve poter disfare
anche questo"*.

---

## Licenza

MIT — tessi liberamente.

---

*Penelope tesse dashboard come la moglie di Ulisse tesseva il sudario di
Laerte: ogni notte le disfa, ogni giorno le rifà — ma il telaio dei tipi
non ammette fili stortati.*

> *«Una dashboard non è mai finita. È sempre in tessitura.*
> *Ma se il telaio è tipato, la tela è coerente a ogni passo —*
> *anche quando si disfa, anche quando si rifà.»*
