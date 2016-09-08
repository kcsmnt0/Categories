open import Cat.Category

module Cat.Functors.Diagonal C where

open import Cat.Functor

open import Cat.Categories.Product C C renaming (productCategory to C×C)
open import Cat.Setoids.Product

open Category C

instance
  diagonalFunctor : Functor C C×C
  diagonalFunctor = record
    { transport = λ x → x , x
    ; isFunctor = record
      { map = λ f → f , f
      ; ≃-map-id = refl , refl
      ; ≃-map-∘ = refl , refl
      ; ≃-map-cong = λ p → p , p
      }
    }

Δ = diagonalFunctor
