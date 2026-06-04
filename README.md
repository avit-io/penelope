# Penelope

<p align="center">
  <img src="logo.svg" width="160" alt="Penelope — il telaio con la tela tessuta di τ, ℳ, ⊢, Σ"/>
</p>

> *Tesse e disfa la tela delle tue metriche — ma il telaio è tipato.*

Verifiable Grafana dashboards in Agda — `Dashboard M`, layout BSP strutturale, integrazione nativa con HenQL.

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
    title  : String
    target : Expr M (queryTypeOf k)
```

Non c'è un campo `.proof : queryTypeOf k ≡ τ`. Il tipo della `target` è
**già** `Expr M (queryTypeOf k)`. Mettere un `Expr M Scalar` in un panel
`TimeSeries` non è un errore di validazione runtime: è un errore di
unificazione del typechecker. La spec è nello shape, non nei commenti.

### La tela non si sovrappone — per costruzione

```agda
data Layout (M : Model) : Set where
  cell   : AnyPanel M                          → Layout M
  above  : (top : Layout M) (bot : Layout M)   → Layout M
  beside : (lft : Layout M) (rgt : Layout M)   → Layout M
```

Una tela è un **albero binary-space-partition**: ogni nodo divide un
rettangolo in due rettangoli disgiunti. *Due foglie non possono
sovrapporsi: vivono in regioni di un partizionamento.* Non c'è una prova
`.non-overlap` da scrivere e verificare — non esiste un costruttore che
produca celle sovrapposte. **È impossibile per sintassi.**

Il renderer cammina l'albero e calcola `gridPos` per ogni foglia
dividendo il viewport a ogni split. È totale per costruzione strutturale:

```agda
renderDashboard : {M : Model} → Dashboard M → String
-- emette Grafana JSON; i gridPos derivati dal walk del Layout.
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
| la tela              | `Layout M`, l'albero BSP delle celle                |
| il filo              | un singolo `Panel M k`                              |
| il telaio            | il typechecker Agda                                 |
| `cell`               | una foglia: un panel posizionato                    |
| `above`              | divisione orizzontale: top sopra bottom             |
| `beside`             | divisione verticale: left accanto a right           |
| `queryTypeOf k`      | il tipo del filo imposto dal panel kind             |
| il pretendente       | una query non tipata che entrerebbe a runtime       |
| disfare la tela      | ri-editare il modulo, ri-typeckeckare                |
| Ulisse che torna     | il deploy di Grafana — la tela esce dal telaio      |

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
open import Penelope.Layout
open import Penelope.Dashboard
open import Penelope.JSON

miaApp : Model
miaApp = record { Time = ℕ ; Val = Float ; Series = String }

errori : Panel miaApp TimeSeries
errori = mkPanel "Errori / s"
  (sumBy ("job" ∷ []) (rate (range "http_requests_errors_total" 5)))

latenza : Panel miaApp TimeSeries
latenza = mkPanel "Latenza"
  (rate (range "http_request_duration_seconds_sum" 5))

budget : Panel miaApp Stat
budget = mkPanel "Budget consumato" (scalar "0.42")

tela : Layout miaApp
tela = above (beside (cell (TimeSeries , errori))
                     (cell (TimeSeries , latenza)))
             (cell (Stat , budget))

salute : Dashboard miaApp
salute = mkDashboard "Salute API" "salute-api" tela

-- renderDashboard salute : String — Grafana JSON pronto.
```

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
│   ├── Panel.agda       # PanelKind · queryTypeOf · record Panel
│   ├── Layout.agda      # data Layout — BSP tree (cell / above / beside)
│   ├── Dashboard.agda   # record Dashboard
│   └── JSON.agda        # renderDashboard — totale, gridPos derivati
├── Examples/
│   └── Tela.agda        # esempio: tre panel, layout BSP, render JSON
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
Penelope.Panel         ← Panel M k (target : Expr M (queryTypeOf k))
Penelope.Layout        ← Layout M (BSP tree, disgiunzione strutturale)
Penelope.Dashboard     ← Dashboard M
Penelope.JSON          ← renderDashboard → Grafana JSON
```

Penelope dipende da HenQL per le query e da Prometea per `Model`. Non sa
nulla di Agdovana — sono progetti sorella che consumano gli stessi tipi
fondazionali per fini diversi (Agdovana → regole di alerting,
Penelope → dashboard).

---

## Garanzie strutturali

Quattro invarianti, **nessuna prova attaccata, nessun runtime check**.

- **Coerenza panel ↔ query** — `queryTypeOf k` è computato dal kind. Il
  campo `target : Expr M (queryTypeOf k)` non ammette altri tipi.
  Sostituire un `TimeSeries` con `Stat` cambia il tipo richiesto della
  target; il typechecker rifiuta il sito di costruzione.
- **Layout non sovrapposto** — `Layout` è un BSP tree. Ogni nodo divide
  un rettangolo in due regioni disgiunte. **Non esiste un costruttore
  che produca celle sovrapposte.** È impossibile per sintassi, non per
  validazione.
- **Layout contiene il viewport** — il renderer parte da un viewport
  fisso (24 × 16) e ogni sotto-chiamata riceve una regione strettamente
  contenuta. Nessuna cella può uscire dal canvas Grafana.
- **Coerenza del modello** — `Dashboard M` ha un solo `M`. Tutti i panel
  della tela condividono lo stesso modello semantico (phantom da
  `Layout M`). Non puoi mescolare panel di modelli diversi nella stessa
  dashboard.

`renderDashboard : Dashboard M → String` è **totale**. Nessun caso
parziale, nessuna eccezione runtime. La tela tessuta è sempre JSON
sintatticamente valido.

---

## Roadmap

In ordine di valore concreto:

1. **`stack : List (Layout M) → Layout M`** — n-ario invece di nidificare
   `above` / `beside`. Resta strutturalmente disgiunto perché ereditato
   dalla decomposizione equa di un rettangolo.
2. **Split pesati** — `above-w : ℕ → ℕ → Layout M → Layout M → Layout M`
   per proporzioni non eque (es. 2/3 + 1/3). Le proporzioni nello shape,
   non in una prova esterna.
3. **Template variables** — il `templating` di Grafana come record tipato,
   con sostituzione nei target delle query.
4. **Datasource non-Prometheus** — Penelope oggi assume `prometheus`.
   Astrarre `Datasource` parallelo a `Model` per Loki, Tempo, ecc.
5. **Layout proof esposto** — fare emergere `Σ (List GridPos) (Disjoint ∧ InCanvas)`
   come output di `walk`, così i consumer downstream possono ragionare
   sull'output e non solo sull'input.

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
