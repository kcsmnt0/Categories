module Cat.Endofunctors.Identity {{C}} where

open import Cat.Category
open import Cat.Functor

open Category

instance
  identityFunctor : Endofunctor C
  identityFunctor = record
    { transport = λ x → x
    ; isFunctor = record
      { map = λ x → x
      ; ≃-map-id = refl C
      ; ≃-map-∘ = refl C
      ; ≃-map-cong = λ x → x
      }
    }
