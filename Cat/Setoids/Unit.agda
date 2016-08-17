module Cat.Setoids.Unit where

open import Cat.Setoid

open import Data.Unit

instance
  unitSetoid : Setoid
  unitSetoid = record
    { Carrier = ⊤
    ; _≈_ = λ _ _ → ⊤
    ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
    }
