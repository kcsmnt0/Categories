open import Cat.Category
open import Cat.Functor

module Cat.NaturalTransformations.Identity {{C D}} (F : Functor C D) where

open import Cat.NaturalTransformation

open Category D
open Functor

instance
  identityNaturalTransformation : NaturalTransformation F F
  identityNaturalTransformation = record
    { transform = id
    ; naturality = λ f →
        begin
          id ∘ map F f
        ≃⟨ idUnitᴸ ⟩
          map F f
        ≃⟨ sym idUnitᴿ ⟩
          map F f ∘ id
        ∎
    }
