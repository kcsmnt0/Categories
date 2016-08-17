open import Cat.Category
open import Cat.Functor
open import Cat.NaturalTransformation

module Cat.NaturalTransformations.Compose
  {{C D}}
  {F G H : Functor C D}
  (β-NT : NaturalTransformation G H)
  (α-NT : NaturalTransformation F G)
  where

open Category D
open Functor

open NaturalTransformation β-NT renaming (transform to β; naturality to β-natural)
open NaturalTransformation α-NT renaming (transform to α; naturality to α-natural)

instance
  _⊚_ : NaturalTransformation F H
  _⊚_ = record
    { transform = β ∘ α
    ; naturality = λ f →
        begin
          (β ∘ α) ∘ map F f
        ≃⟨ sym assoc ⟩
          β ∘ (α ∘ map F f)
        ≃⟨ cong⟨∘ α-natural f ⟩ ⟩
          β ∘ (map G f ∘ α)
        ≃⟨ assoc ⟩
          (β ∘ map G f) ∘ α
        ≃⟨ cong⟨ β-natural f ∘⟩ ⟩
          (map H f ∘ β) ∘ α
        ≃⟨ sym assoc ⟩
          map H f ∘ (β ∘ α)
        ∎
    }
