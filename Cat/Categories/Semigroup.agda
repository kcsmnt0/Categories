module Cat.Categories.Semigroup where

open import Cat.Category
open import Cat.Setoid

open import Cat.Categories.Setoid as S using (setoidCategory; _§_; _$_; cong-▸)
open import Cat.Structures.Semigroup

open Category setoidCategory
open Semigroup

infixr 0 _▸_
record _▸_ (A B : Semigroup) : Set where
  field
    homomorphism : Carrier A S.▸ Carrier B
    homomorphismPreservesAppend : ∀ {x y} → Carrier B ⟪
      homomorphism § (append A § x § y) ≈ append B § (homomorphism § x) § (homomorphism § y) ⟫

open _▸_ public

infixr 0 _↦_
_↦_ : Semigroup → Semigroup → Setoid
A ↦ B = record
  { Carrier = A ▸ B
  ; _≈_ = λ f g → (Carrier A S.↦ Carrier B) ⟪ homomorphism f ≈ homomorphism g ⟫
  ; isEquivalence = record
    { refl = λ {f} → refl {f = homomorphism f}
    ; sym = λ {f g} → sym {f = homomorphism f} {g = homomorphism g}
    ; trans = λ {f g h} → trans {f = homomorphism f} {g = homomorphism g} {h = homomorphism h}
    }
  }

instance
  semigroupCategory : Category
  semigroupCategory = record
    { Carrier = Semigroup
    ; _⇒_ = _↦_
    ; isCategory = record
      { id = λ {A} → record
        { homomorphism = id
        ; homomorphismPreservesAppend = refl {f = append A S.$ _} _ 
        }
      ; _∘_ = λ {A B C} g f → record
        { homomorphism = homomorphism g ∘ homomorphism f
        ; homomorphismPreservesAppend =
            Setoid.trans (Carrier C)
              (cong-▸ (homomorphism g) (homomorphismPreservesAppend f))
              (homomorphismPreservesAppend g)
        }
      ; cong⟨_∘_⟩ = λ {A B C f g h i} q p x →
          Setoid.trans (Carrier C)
            (cong-▸ (homomorphism h) (p x))
            (q _)
      ; idUnitᴸ = λ {_ _ f} → refl {f = homomorphism f}
      ; idUnitᴿ = λ {_ _ f} → refl {f = homomorphism f}
      ; assoc = λ {_ _ _ _ f g h} → refl {f = homomorphism h ∘ homomorphism g ∘ homomorphism f}
      }
    }
