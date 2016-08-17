module Cat.Setoids.Empty where

open import Cat.Setoid

open import Data.Empty

instance
  emptySetoid : Setoid
  emptySetoid = record
    { Carrier = ⊥
    ; _≈_ = λ ()
    ; isEquivalence = record { refl = λ {} ; sym = λ {} ; trans = λ {} }
    }
