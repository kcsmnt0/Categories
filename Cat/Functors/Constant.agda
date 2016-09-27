open import Cat.Category

module Cat.Functors.Constant {{C D : Category}} where

open import Cat.Functor

open Category D

instance
  constantFunctor : [ D ] → Functor C D
  constantFunctor x = record
    { transport = λ _ → x
    ; isFunctor = record
      { map = λ _ → id
      ; ≃-map-id = refl
      ; ≃-map-∘ = idUnitᴸ
      ; ≃-map-cong = λ _ → refl
      }
    }

δ = constantFunctor
