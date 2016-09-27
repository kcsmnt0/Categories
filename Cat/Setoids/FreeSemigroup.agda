{-# OPTIONS --type-in-type #-}

module Cat.Setoids.FreeSemigroup where

open import Cat.Setoid

open import Cat.Structures.Semigroup

infixr 4 _⟦⊕⟧_
data FreeSemigroup (A : Setoid) : Set where
  ⟦_⟧ : ⟨ A ⟩ → FreeSemigroup A
  _⟦⊕⟧_ : FreeSemigroup A → FreeSemigroup A → FreeSemigroup A

infix 2 _≊_
data _≊_ {A} : FreeSemigroup A → FreeSemigroup A → Set where
  ⟦_⟧ : ∀ {x y} → A ⟪ x ≈ y ⟫ → ⟦ x ⟧ ≊ ⟦ y ⟧
  ≊-refl : ∀ {x} → x ≊ x
  ≊-sym : ∀ {x y} → x ≊ y → y ≊ x
  ≊-trans : ∀ {x y z} → x ≊ y → y ≊ z → x ≊ z
  ≊-cong⟨_⊕_⟩ : ∀ {x y z w} → x ≊ y → z ≊ w → (x ⟦⊕⟧ z) ≊ (y ⟦⊕⟧ w)
  ≊-assoc-⊕ : ∀ {x y z} → x ⟦⊕⟧ (y ⟦⊕⟧ z) ≊ (x ⟦⊕⟧ y) ⟦⊕⟧ z

freeSemigroupSetoid : Setoid → Setoid
freeSemigroupSetoid A = record
  { Carrier = FreeSemigroup A
  ; _≈_ = _≊_
  ; isEquivalence = record
    { refl = ≊-refl
    ; sym = ≊-sym
    ; trans = ≊-trans
    }
  }

freeSemigroupSemigroup : Setoid → Semigroup
freeSemigroupSemigroup A = record
  { Carrier = freeSemigroupSetoid A
  ; isSemigroup = record
    { append = record
      { _$_ = λ x → record
        { _$_ = x ⟦⊕⟧_
        ; cong-▸ = ≊-cong⟨ refl ⊕_⟩
        }
      ; cong-▸ = λ p _ → ≊-cong⟨ p ⊕ refl ⟩
      }
    ; cong-append = ≊-cong⟨_⊕_⟩
    ; assoc-append = ≊-assoc-⊕
    }
  }
  where open Setoid (freeSemigroupSetoid A)
