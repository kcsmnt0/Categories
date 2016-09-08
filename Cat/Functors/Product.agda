open import Cat.Category

module Cat.Functors.Product {{C D}} where

open import Cat.Functor

open import Cat.Categories.Product C D
open import Cat.Setoids.Product

open Category {{…}}

takeFstFunctor : Functor productCategory C
takeFstFunctor = record
  { transport = fst
  ; isFunctor = record
    { map = fst
    ; ≃-map-id = refl
    ; ≃-map-∘ = refl
    ; ≃-map-cong = fst
    }
  }

takeSndFunctor : Functor productCategory D
takeSndFunctor = record
  { transport = snd
  ; isFunctor = record
    { map = snd
    ; ≃-map-id = refl
    ; ≃-map-∘ = refl
    ; ≃-map-cong = snd
    }
  }
