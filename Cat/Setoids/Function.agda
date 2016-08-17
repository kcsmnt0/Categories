module Cat.Setoids.Function A B where

open import Cat.Setoid

open import Relation.Binary.PropositionalEquality

instance
  functionSetoid : Setoid
  functionSetoid = record
    { Carrier = A → B
    ; _≈_ = λ f g → ∀ x → f x ≡ g x
    ; isEquivalence = record
      { refl = λ _ → refl
      ; sym = λ p x → sym (p x)
      ; trans = λ p q x → trans (p x) (q x)
      }
    }

