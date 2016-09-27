module Cat.Setoids.Setoid where

open import Cat.Category
open import Cat.Setoid renaming (module Setoid to S)
open import Cat.Isomorphism

open import Cat.Categories.Setoid

open Category setoidCategory

⇔-refl : ∀ {A} → A ⇔ A
⇔-refl {A} = record
  { right = id
  ; left = id
  ; isIsomorphism = record
    { cancelLR = λ _ → S.refl A
    ; cancelRL = λ _ → S.refl A
    }
  }

⇔-sym : ∀ {A B} → A ⇔ B → B ⇔ A
⇔-sym f = record
  { right = left
  ; left = right
  ; isIsomorphism = record
    { cancelLR = cancelRL
    ; cancelRL = cancelLR
    }
  }
  where open Isomorphism f

⇔-trans : ∀ {A B C} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans {A} {B} {C} f g = record
  { right = right g ∘ right f
  ; left = left f ∘ left g
  ; isIsomorphism = record
    { cancelLR = λ x → S.trans C (cong-▸ (right g) (cancelLR f (left g $ x))) (cancelLR g x)
    ; cancelRL = λ x → S.trans A (cong-▸ (left f) (cancelRL g (right f $ x))) (cancelRL f x)
    }
  }
  where open Isomorphism

instance
  setoidSetoid : Setoid
  setoidSetoid = record
    { Carrier = Setoid
    ; _≈_ = _⇔_
    ; isEquivalence = record
      { refl = ⇔-refl
      ; sym = ⇔-sym
      ; trans = ⇔-trans
      }
    }
