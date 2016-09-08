{-# OPTIONS --type-in-type #-}

-- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.387.4022&rep=rep1&type=pdf

module Cat.Setoids.STLC where

open import Cat.Setoid

open import Cat.Categories.Setoid
open import Cat.Setoids.HVec as H using (HVec; []; _∷_; lookupH; ≊-lookupH-cong; ≊-ope-subst-∈; opeStripH; headH; tailH)

open import Data.Fin
open import Data.List
open import Data.Nat
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality as PE using (subst)

open Setoid

infix 3 _∈_
data _∈_ {A} : A → List A → Set where
  here : ∀ {x xs} → x ∈ (x ∷ xs)
  there : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

infix 4 _⊆_
data _⊆_ {A} : List A → List A → Set where
  stop : [] ⊆ []
  keep : ∀ {x xs ys} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
  skip : ∀ {x xs ys} → xs ⊆ ys → xs ⊆ (x ∷ ys)

⊆-id : ∀ {A} {xs : List A} → xs ⊆ xs
⊆-id {xs = []} = stop
⊆-id {xs = x ∷ xs} = keep ⊆-id

⊆-weaken : ∀ {A x} {xs : List A} → xs ⊆ (x ∷ xs)
⊆-weaken = skip ⊆-id

⊆-map-∈ : ∀ {A x} {xs ys : List A} → xs ⊆ ys → x ∈ xs → x ∈ ys
⊆-map-∈ (keep sub) here = here
⊆-map-∈ (keep sub) (there i) = there (⊆-map-∈ sub i)
⊆-map-∈ (skip sub) i = there (⊆-map-∈ sub i)

infixr 0 _▹_
data Type : Set where
  ⟦_⟧ : Setoid → Type
  _▹_ : Type → Type → Type

type : Type → Setoid
type ⟦ A ⟧ = A
type (A ▹ B) = type A ↦ type B

infixl 2 _∙_
infix 3 _⊢_
data _⊢_ : List Setoid → Setoid → Set where
  ⟦_⟧ : ∀ {A g} → ⟨ A ⟩ → g ⊢ A
  var : ∀ {A g} → A ∈ g → g ⊢ A
  _∙_ : ∀ {A B g} → g ⊢ (A ↦ B) → g ⊢ A → g ⊢ B
  ƛ_ : ∀ {A B g} → (A ∷ g) ⊢ B → g ⊢ (A ↦ B)

⊢-dilute : ∀ {A g g′} → g ⊆ g′ → g ⊢ A → g′ ⊢ A
⊢-dilute g⊆g′ ⟦ x ⟧ = ⟦ x ⟧
⊢-dilute g⊆g′ (var i) = var (⊆-map-∈ g⊆g′ i)
⊢-dilute g⊆g′ (s ∙ t) = ⊢-dilute g⊆g′ s ∙ ⊢-dilute g⊆g′ t
⊢-dilute g⊆g′ (ƛ t) = ƛ ⊢-dilute (keep g⊆g′) t

-- ⊢-weaken : ∀ {A B g} → g ⊢ B → (A ∷ g) ⊢ B
-- ⊢-weaken = ⊢-dilute ⊆-weaken

_—_ : ∀ {A x} (xs : List A) → x ∈ xs → List A
(x ∷ xs) — here = xs
(x ∷ xs) — there i = x ∷ (xs — i)

∈-weaken : ∀ {A} {x y} {xs : List A} (i : x ∈ xs) → y ∈ xs — i → y ∈ xs
∈-weaken here i = there i
∈-weaken (there i) here = here
∈-weaken (there i) (there j) = there (∈-weaken i j)

infix 1 _∈≟_
data _∈≟_ {A} : ∀ {x y} {xs : List A} → x ∈ xs → y ∈ xs → Set where
  same : ∀ {x xs} {i : x ∈ xs} → i ∈≟ i
  diff : ∀ {x y xs} (i : x ∈ xs) (j : y ∈ (xs — i)) → i ∈≟ ∈-weaken i j

-- i mean what kind of name is this thing supposed to have
_∈≟?_ : ∀ {A x y} {xs : List A} (i : x ∈ xs) (j : y ∈ xs) → i ∈≟ j
here ∈≟? here = same
here ∈≟? there j = diff here j
there i ∈≟? here = diff (there i) here
there i ∈≟? there j with i ∈≟? j
there i ∈≟? there .i | same = same
there i ∈≟? there .(∈-weaken i j) | diff .i j = diff (there i) (there j)

⊢-weaken : ∀ {A B g} (i : A ∈ g) → (g — i) ⊢ B → g ⊢ B
⊢-weaken i ⟦ x ⟧ = ⟦ x ⟧
⊢-weaken i (var j) = var (∈-weaken i j)
⊢-weaken i (s ∙ t) = ⊢-weaken i s ∙ ⊢-weaken i t
⊢-weaken i (ƛ t) = ƛ ⊢-weaken (there i) t

⊢-subst : ∀ {A B g} → g ⊢ A → (j : B ∈ g) → g — j ⊢ B → g — j ⊢ A
⊢-subst ⟦ x ⟧ j t = ⟦ x ⟧
⊢-subst (var i) j t with j ∈≟? i
⊢-subst (var i) .i t | same = t
⊢-subst (var .(∈-weaken i j)) i t | diff .i j = var j
⊢-subst (s ∙ t) j u = ⊢-subst s j u ∙ ⊢-subst t j u
⊢-subst (ƛ s) j t = ƛ ⊢-subst s (there j) (⊢-weaken here t)

data Env : List Setoid → Set where
  [] : Env []
  _∷_ : ∀ {g A} → ⟨ A ⟩ → Env g → Env (A ∷ g)

data _≅_ : ∀ {g} → Env g → Env g → Set where
  [] : [] ≅ []
  _∷_ : ∀ {A g x y xs ys} → A ⟪ x ≈ y ⟫ → _≅_ {g} xs ys → (_∷_ {A = A} x xs) ≅ (y ∷ ys)

≅-refl : ∀ {g} {p : Env g} → p ≅ p
≅-refl {[]} {[]} = []
≅-refl {A ∷ _} {_ ∷ _} = refl A ∷ ≅-refl

index : ∀ {A g} → A ∈ g → Env g → ⟨ A ⟩
index here (x ∷ p) = x
index (there i) (x ∷ p) = index i p

≅-cong-index : ∀ {A g} {p p′ : Env g} (i : A ∈ g) → p ≅ p′ → A ⟪ index i p ≈ index i p′ ⟫
≅-cong-index here (x ∷ q) = x
≅-cong-index (there i) (x ∷ q) = ≅-cong-index i q

infix 1 _≊_
data _≊_ : ∀ {A g} → g ⊢ A → g ⊢ A → Set where
  ≊-refl : ∀ {A g} {t : g ⊢ A} → t ≊ t
  ≊-sym : ∀ {A g} {s t : g ⊢ A} → s ≊ t → t ≊ s
  ≊-trans : ∀ {A g} {s t u : g ⊢ A} → s ≊ t → t ≊ u → s ≊ u

  ≊-ƛ : ∀ {A B g} {s t : (A ∷ g) ⊢ B} → s ≊ t → ƛ s ≊ ƛ t
  ≊-∙ : ∀ {A B g} {s s′ : g ⊢ (A ↦ B)} {t t′ : g ⊢ A} → s ≊ s′ → t ≊ t′ → s ∙ t ≊ s′ ∙ t′
  ≊-β : ∀ {A B g} {s : (A ∷ g) ⊢ B} {t : g ⊢ A} → (ƛ s) ∙ t ≊ ⊢-subst s here t
  ≊-η : ∀ {A B g} {t : (A ∷ g) ⊢ B} → (ƛ ⊢-weaken here t) ∙ var here ≊ t
