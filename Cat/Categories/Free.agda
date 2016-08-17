{-# OPTIONS --type-in-type #-}

module Cat.Categories.Free {A} (R : A → A → Set) where

open import Cat.Category
open import Cat.Functor
open import Cat.Setoid

open Category {{…}}

infixr 0 _⟦⇒⟧_
infixr 8 _⟦∘⟧_
data _⟦⇒⟧_ : A → A → Set where
  ⟦_⟧ : ∀ {a b} → R a b → a ⟦⇒⟧ b
  ⟦id⟧ : ∀ {a} → a ⟦⇒⟧ a
  _⟦∘⟧_ : ∀ {a b c} → b ⟦⇒⟧ c → a ⟦⇒⟧ b → a ⟦⇒⟧ c

infix 4 _⟦≃⟧_
data _⟦≃⟧_ : ∀ {a b} → a ⟦⇒⟧ b → a ⟦⇒⟧ b → Set where
  ⟦refl⟧ : ∀ {a b} {f : a ⟦⇒⟧ b} → f ⟦≃⟧ f
  ⟦sym⟧ : ∀ {a b} {f g : a ⟦⇒⟧ b} → f ⟦≃⟧ g → g ⟦≃⟧ f
  ⟦trans⟧ : ∀ {a b} {f g h : a ⟦⇒⟧ b} → f ⟦≃⟧ g → g ⟦≃⟧ h → f ⟦≃⟧ h

  ⟦cong⟨_∘_⟩⟧ : ∀ {a b c} {f g : a ⟦⇒⟧ b} {h i : b ⟦⇒⟧ c} → h ⟦≃⟧ i → f ⟦≃⟧ g → h ⟦∘⟧ f ⟦≃⟧ i ⟦∘⟧ g
  ⟦idUnitᴸ⟧ : ∀ {a b} {f : a ⟦⇒⟧ b} → ⟦id⟧ ⟦∘⟧ f ⟦≃⟧ f
  ⟦idUnitᴿ⟧ : ∀ {a b} {f : a ⟦⇒⟧ b} → f ⟦∘⟧ ⟦id⟧ ⟦≃⟧ f
  ⟦assoc⟧ : ∀ {a b c d} {f : a ⟦⇒⟧ b} {g : b ⟦⇒⟧ c} {h : c ⟦⇒⟧ d} → h ⟦∘⟧ (g ⟦∘⟧ f) ⟦≃⟧ (h ⟦∘⟧ g) ⟦∘⟧ f

-- as in "make closed", not "nearby"
Close : A → A → Setoid
Close a b = record
  { Carrier = a ⟦⇒⟧ b
  ; _≈_ = _⟦≃⟧_
  ; isEquivalence = record
      { refl = ⟦refl⟧
      ; sym = ⟦sym⟧
      ; trans = ⟦trans⟧
      }
  }

instance
  freeCategory : Category
  freeCategory = record
    { _⇒_ = Close
    ; isCategory = record
        { id = ⟦id⟧
        ; _∘_ = _⟦∘⟧_
        ; cong⟨_∘_⟩ = ⟦cong⟨_∘_⟩⟧
        ; idUnitᴸ = ⟦idUnitᴸ⟧
        ; idUnitᴿ = ⟦idUnitᴿ⟧
        ; assoc = ⟦assoc⟧
        }
    }
