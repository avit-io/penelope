module Penelope.Tiling where

-- ╔════════════════════════════════════════════════════════════════════╗
-- ║  Livello geometrico — tassellamenti slicing del rettangolo.        ║
-- ║                                                                    ║
-- ║  Modulo INDIPENDENTE da Grafana: nessun import di Model, PromType, ║
-- ║  PanelKind. Solo aritmetica di rettangoli e tagli a ghigliottina.  ║
-- ║                                                                    ║
-- ║  La classe di tassellamenti rappresentata è quella degli SLICING   ║
-- ║  FLOORPLAN (partizioni guillotine): ogni partizione del rettangolo ║
-- ║  si ottiene per tagli completi orizzontali o verticali ricorsivi.  ║
-- ║  Il pinwheel a 5 rettangoli NON è rappresentabile, perché richiede ║
-- ║  un taglio non-guillotine.                                         ║
-- ║                                                                    ║
-- ║  RAPPRESENTAZIONE. Tiling è indicizzato sui 4 campi ℕ (x, y, w, h) ║
-- ║  anziché su Rect (l'unificazione di indici-record si blocca in     ║
-- ║  Agda 2.8). Un cut è parametrizzato dalle SOTTO-DIMENSIONI dei due ║
-- ║  figli (ht hb per hcut, wl wr per vcut), suc-indicizzate: il padre ║
-- ║  ha altezza (suc ht + suc hb), entrambi i figli hanno altezza ≥ 1. ║
-- ║  L'invariante min-size dei figli è DEFINIZIONALE.                  ║
-- ║                                                                    ║
-- ║  La posizione del taglio è equivalente a una Fin (h ∸ 1): scegliere║
-- ║  k : Fin (h ∸ 1) corrisponde a scegliere (ht hb) con suc ht +      ║
-- ║  suc hb = h. La presentazione suc-additiva evita l'uso di ∸, che   ║
-- ║  non è iniettivo e impedisce l'unificazione dei pattern.           ║
-- ╚════════════════════════════════════════════════════════════════════╝

open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-monoʳ-≤; m≤m+n; +-assoc)
open import Data.Empty
  using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong)

-- ─────────────────────────────────────────────────────────────────────
-- Rect: rettangolo posizionato. Esposto come record per la decorazione.
-- ─────────────────────────────────────────────────────────────────────

record Rect : Set where
  constructor mkRect
  field x y w h : ℕ
open Rect public

-- ─────────────────────────────────────────────────────────────────────
-- Tiling: slicing floorplan intrinseco, indicizzato sui 4 campi ℕ.
--
-- Per hcut: ht, hb sono le altezze-meno-uno dei due figli; il padre ha
-- altezza (suc ht + suc hb). Entrambi i figli hanno altezza ≥ 1 PER
-- COSTRUZIONE (struttura suc). Per vcut: simmetrico su w.
-- ─────────────────────────────────────────────────────────────────────

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

-- Surface wrapper: un Tiling "del" rettangolo r (per la decorazione).
TilingOf : Rect → Set
TilingOf r = Tiling (x r) (y r) (w r) (h r)

-- ─────────────────────────────────────────────────────────────────────
-- Leaf: indirizzo di una foglia (cella) dentro un Tiling.
-- ─────────────────────────────────────────────────────────────────────

data Leaf : ∀ {x y w h} → Tiling x y w h → Set where
  here   : ∀ {x y w h} → Leaf (tile {x} {y} {w} {h})
  topL   : ∀ {x y w} {ht hb : ℕ}
             {tt : Tiling x y w (suc ht)}
             {tb : Tiling x (y + suc ht) w (suc hb)}
         → Leaf tt → Leaf (hcut tt tb)
  botL   : ∀ {x y w} {ht hb : ℕ}
             {tt : Tiling x y w (suc ht)}
             {tb : Tiling x (y + suc ht) w (suc hb)}
         → Leaf tb → Leaf (hcut tt tb)
  leftL  : ∀ {x y h} {wl wr : ℕ}
             {tl : Tiling x y (suc wl) h}
             {tr : Tiling (x + suc wl) y (suc wr) h}
         → Leaf tl → Leaf (vcut tl tr)
  rightL : ∀ {x y h} {wl wr : ℕ}
             {tl : Tiling x y (suc wl) h}
             {tr : Tiling (x + suc wl) y (suc wr) h}
         → Leaf tr → Leaf (vcut tl tr)

-- ─────────────────────────────────────────────────────────────────────
-- place: piazza una foglia, restituendo il Rect che occupa.
-- ─────────────────────────────────────────────────────────────────────

place : ∀ {x y w h} (t : Tiling x y w h) → Leaf t → Rect
place {x} {y} {w} {h} tile here = mkRect x y w h
place (hcut tt _ ) (topL l)     = place tt l
place (hcut _  tb) (botL l)     = place tb l
place (vcut tl _ ) (leftL l)    = place tl l
place (vcut _  tr) (rightL l)   = place tr l

-- ─────────────────────────────────────────────────────────────────────
-- Containment: r ⊆ r' significa "r è contenuto in r'".
-- ─────────────────────────────────────────────────────────────────────

record _⊆_ (r r' : Rect) : Set where
  field
    ⊆-x  : x r' ≤ x r
    ⊆-y  : y r' ≤ y r
    ⊆-xr : x r + w r ≤ x r' + w r'
    ⊆-yb : y r + h r ≤ y r' + h r'
open _⊆_ public

⊆-refl : ∀ {r} → r ⊆ r
⊆-refl = record
  { ⊆-x  = ≤-refl ; ⊆-y  = ≤-refl
  ; ⊆-xr = ≤-refl ; ⊆-yb = ≤-refl
  }

⊆-trans : ∀ {a b c} → a ⊆ b → b ⊆ c → a ⊆ c
⊆-trans ab bc = record
  { ⊆-x  = ≤-trans (⊆-x bc) (⊆-x ab)
  ; ⊆-y  = ≤-trans (⊆-y bc) (⊆-y ab)
  ; ⊆-xr = ≤-trans (⊆-xr ab) (⊆-xr bc)
  ; ⊆-yb = ≤-trans (⊆-yb ab) (⊆-yb bc)
  }

-- ─────────────────────────────────────────────────────────────────────
-- Containment di ogni parte nel suo parent — prove banali sui ≤.
-- ─────────────────────────────────────────────────────────────────────

topPart-⊆ : ∀ x y w ht hb
          → mkRect x y w (suc ht) ⊆ mkRect x y w (suc ht + suc hb)
topPart-⊆ x y w ht hb = record
  { ⊆-x  = ≤-refl
  ; ⊆-y  = ≤-refl
  ; ⊆-xr = ≤-refl
  ; ⊆-yb = +-monoʳ-≤ y (m≤m+n (suc ht) (suc hb))
  }

botPart-⊆ : ∀ x y w ht hb
          → mkRect x (y + suc ht) w (suc hb) ⊆ mkRect x y w (suc ht + suc hb)
botPart-⊆ x y w ht hb = record
  { ⊆-x  = ≤-refl
  ; ⊆-y  = m≤m+n y (suc ht)
  ; ⊆-xr = ≤-refl
  ; ⊆-yb = ≤-reflexive (+-assoc y (suc ht) (suc hb))
  }

leftPart-⊆ : ∀ x y h wl wr
           → mkRect x y (suc wl) h ⊆ mkRect x y (suc wl + suc wr) h
leftPart-⊆ x y h wl wr = record
  { ⊆-x  = ≤-refl
  ; ⊆-y  = ≤-refl
  ; ⊆-xr = +-monoʳ-≤ x (m≤m+n (suc wl) (suc wr))
  ; ⊆-yb = ≤-refl
  }

rightPart-⊆ : ∀ x y h wl wr
            → mkRect (x + suc wl) y (suc wr) h ⊆ mkRect x y (suc wl + suc wr) h
rightPart-⊆ x y h wl wr = record
  { ⊆-x  = m≤m+n x (suc wl)
  ; ⊆-y  = ≤-refl
  ; ⊆-xr = ≤-reflexive (+-assoc x (suc wl) (suc wr))
  ; ⊆-yb = ≤-refl
  }

-- ─────────────────────────────────────────────────────────────────────
-- Lemma: ogni foglia piazzata è contenuta nel rettangolo del Tiling.
-- ─────────────────────────────────────────────────────────────────────

contained : ∀ {x y w h} (t : Tiling x y w h) (l : Leaf t)
          → place t l ⊆ mkRect x y w h
contained                  tile          here     = ⊆-refl
contained {x} {y} {w} (hcut {ht = ht} {hb = hb} tt _ ) (topL l) =
  ⊆-trans (contained tt l) (topPart-⊆ x y w ht hb)
contained {x} {y} {w} (hcut {ht = ht} {hb = hb} _  tb) (botL l) =
  ⊆-trans (contained tb l) (botPart-⊆ x y w ht hb)
contained {x} {y} {h = h} (vcut {wl = wl} {wr = wr} tl _ ) (leftL l) =
  ⊆-trans (contained tl l) (leftPart-⊆ x y h wl wr)
contained {x} {y} {h = h} (vcut {wl = wl} {wr = wr} _  tr) (rightL l) =
  ⊆-trans (contained tr l) (rightPart-⊆ x y h wl wr)

-- ─────────────────────────────────────────────────────────────────────
-- Disjointness: due rettangoli sono disgiunti se uno è interamente a
-- sinistra, a destra, sopra o sotto l'altro (axis-aligned).
-- ─────────────────────────────────────────────────────────────────────

data Disjoint : Rect → Rect → Set where
  leftOf  : ∀ {r₁ r₂} → x r₁ + w r₁ ≤ x r₂ → Disjoint r₁ r₂
  rightOf : ∀ {r₁ r₂} → x r₂ + w r₂ ≤ x r₁ → Disjoint r₁ r₂
  above   : ∀ {r₁ r₂} → y r₁ + h r₁ ≤ y r₂ → Disjoint r₁ r₂
  below   : ∀ {r₁ r₂} → y r₂ + h r₂ ≤ y r₁ → Disjoint r₁ r₂

Disjoint-sym : ∀ {a b} → Disjoint a b → Disjoint b a
Disjoint-sym (leftOf  p) = rightOf p
Disjoint-sym (rightOf p) = leftOf  p
Disjoint-sym (above   p) = below   p
Disjoint-sym (below   p) = above   p

-- Se a ⊆ b e c ⊆ d, e b e d sono disgiunti, allora a e c lo sono.
Disjoint-mono : ∀ {a b c d}
              → a ⊆ b → c ⊆ d → Disjoint b d → Disjoint a c
Disjoint-mono ab cd (leftOf  p) =
  leftOf  (≤-trans (⊆-xr ab) (≤-trans p (⊆-x cd)))
Disjoint-mono ab cd (rightOf p) =
  rightOf (≤-trans (⊆-xr cd) (≤-trans p (⊆-x ab)))
Disjoint-mono ab cd (above   p) =
  above   (≤-trans (⊆-yb ab) (≤-trans p (⊆-y cd)))
Disjoint-mono ab cd (below   p) =
  below   (≤-trans (⊆-yb cd) (≤-trans p (⊆-y ab)))

-- I due figli di hcut/vcut sono disgiunti per costruzione (≤-refl).
topBotPart-Disjoint : ∀ x y w ht hb
                    → Disjoint (mkRect x y w (suc ht))
                               (mkRect x (y + suc ht) w (suc hb))
topBotPart-Disjoint x y w ht hb = above ≤-refl

leftRightPart-Disjoint : ∀ x y h wl wr
                       → Disjoint (mkRect x y (suc wl) h)
                                  (mkRect (x + suc wl) y (suc wr) h)
leftRightPart-Disjoint x y h wl wr = leftOf ≤-refl

-- ─────────────────────────────────────────────────────────────────────
-- Lemma: due foglie distinte di un Tiling occupano rettangoli disgiunti.
-- ─────────────────────────────────────────────────────────────────────

disjoint : ∀ {x y w h} (t : Tiling x y w h) (l₁ l₂ : Leaf t)
         → l₁ ≢ l₂ → Disjoint (place t l₁) (place t l₂)

-- tile: l'unica foglia è here. l₁ = l₂ = here → contraddice l₁ ≢ l₂.
disjoint tile here here neq = ⊥-elim (neq refl)

-- hcut: 4 combinazioni di (topL/botL).
disjoint (hcut tt tb) (topL l₁) (topL l₂) neq =
  disjoint tt l₁ l₂ (λ eq → neq (cong topL eq))
disjoint {x} {y} {w} (hcut {ht = ht} {hb = hb} tt tb) (topL l₁) (botL l₂) _ =
  Disjoint-mono (contained tt l₁) (contained tb l₂)
                (topBotPart-Disjoint x y w ht hb)
disjoint {x} {y} {w} (hcut {ht = ht} {hb = hb} tt tb) (botL l₁) (topL l₂) _ =
  Disjoint-sym
    (Disjoint-mono (contained tt l₂) (contained tb l₁)
                   (topBotPart-Disjoint x y w ht hb))
disjoint (hcut tt tb) (botL l₁) (botL l₂) neq =
  disjoint tb l₁ l₂ (λ eq → neq (cong botL eq))

-- vcut: 4 combinazioni di (leftL/rightL).
disjoint (vcut tl tr) (leftL l₁) (leftL l₂) neq =
  disjoint tl l₁ l₂ (λ eq → neq (cong leftL eq))
disjoint {x} {y} {h = h} (vcut {wl = wl} {wr = wr} tl tr) (leftL l₁) (rightL l₂) _ =
  Disjoint-mono (contained tl l₁) (contained tr l₂)
                (leftRightPart-Disjoint x y h wl wr)
disjoint {x} {y} {h = h} (vcut {wl = wl} {wr = wr} tl tr) (rightL l₁) (leftL l₂) _ =
  Disjoint-sym
    (Disjoint-mono (contained tl l₂) (contained tr l₁)
                   (leftRightPart-Disjoint x y h wl wr))
disjoint (vcut tl tr) (rightL l₁) (rightL l₂) neq =
  disjoint tr l₁ l₂ (λ eq → neq (cong rightL eq))
