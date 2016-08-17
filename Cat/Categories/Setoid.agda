{-# OPTIONS --type-in-type #-}

module Cat.Categories.Setoid where

open import Cat.Category
open import Cat.Setoid
open import Cat.Setoids.SetSetoid

open Setoid

infixr 0 _▸_
record _▸_ (A B : Setoid) : Set where
  infixr 1 _$_

  field
    _$_ : ⟨ A ⟩ → ⟨ B ⟩
    cong-▸ : ∀ {x y} → A ⟪ x ≈ y ⟫ → B ⟪ _$_ x ≈ _$_ y ⟫

open _▸_ public

infixr 0 _↦_
_↦_ : Setoid → Setoid → Setoid
A ↦ B = record
  { Carrier = A ▸ B
  ; _≈_ = λ f g → ∀ x → B ⟪ f $ x ≈ g $ x ⟫
  ; isEquivalence = record
    { refl = λ _ → refl B
    ; sym = λ p x → sym B (p x)
    ; trans = λ p q x → trans B (p x) (q x)
    }
  }

instance
  setoidCategory : Category
  setoidCategory = record
    { _⇒_ = _↦_
    ; isCategory = record
        { id = record { _$_ = λ x → x ; cong-▸ = λ x → x }
        ; _∘_ = λ g f → record
        { _$_ = λ x → g $ f $ x
        ; cong-▸ = λ p → cong-▸ g (cong-▸ f p)
        }
        ; idUnitᴸ = λ {_}{b} x → refl b
        ; idUnitᴿ = λ {_}{b} x → refl b
        ; assoc = λ {_}{_}{_}{d} x → refl d
        ; cong⟨_∘_⟩ = λ { {c = c} {h = h} q p x → trans c (cong-▸ h (p x)) (q _) }
        }
    }
