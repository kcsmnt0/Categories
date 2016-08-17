module Cat.Setoids.SetSetoid A where

open import Cat.Setoid

open import Relation.Binary.PropositionalEquality

instance
  setSetoid : Setoid
  setSetoid = record
    { Carrier = A
    ; _≈_ = _≡_
    ; isEquivalence = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    }
