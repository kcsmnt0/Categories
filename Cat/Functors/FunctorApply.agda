open import Cat.Category
open import Cat.Functor

-- is there a real name for this?
-- the functor from (Functor C D × C) to D
module Cat.Functors.FunctorApply C D where

open import Cat.Categories.Functor C D
open import Cat.Categories.Product functorCategory C
open import Cat.NaturalTransformation

open Category D
open Functor
open NaturalTransformation

open import Data.Product using (_,_)

instance
  functorApplyFunctor : Functor productCategory D
  functorApplyFunctor = record
    { isFunctor = record
      { map = λ { {F , a} (α , h) → transform α ∘ map F h } 
      ; ≃-map-id = λ { {F , a} → trans cong⟨∘ ≃-map-id F ⟩ idUnitᴸ }
      ; ≃-map-cong = λ { {F , a} (p , q) → cong⟨ p ∘ ≃-map-cong F q ⟩ }
      ; ≃-map-∘ = λ
          { {F , a} {G , b} {H , c} {α , h} {β , i} →
              begin
                (transform β ∘ map G i) ∘ (transform α ∘ map F h)
              ≃⟨ sym assoc ⟩
                transform β ∘ (map G i ∘ (transform α ∘ map F h))
              ≃⟨ cong⟨∘ assoc ⟩ ⟩
                transform β ∘ ((map G i ∘ transform α) ∘ map F h)
              ≃⟨ cong⟨∘ cong⟨ sym (naturality α i) ∘⟩ ⟩ ⟩
                transform β ∘ ((transform α ∘ map F i) ∘ map F h)
              ≃⟨ cong⟨∘ sym assoc ⟩ ⟩
                transform β ∘ (transform α ∘ (map F i ∘ map F h))
              ≃⟨ assoc ⟩
                (transform β ∘ transform α) ∘ (map F i ∘ map F h)
              ≃⟨ cong⟨∘ ≃-map-∘ F ⟩ ⟩
                (transform β ∘ transform α) ∘ (map F (Category._∘_ C i h))
              ∎
          }
      }
    }
