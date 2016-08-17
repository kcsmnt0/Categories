open import Cat.Category
open import Cat.Functor

module Cat.Cone {{I C}} (D : Functor I C) where

open import Cat.NaturalTransformation
open import Cat.Setoid

open import Cat.Functors.Constant

record IsCone (c : [ C ]) : Set where
  open Category {{…}}
  open Functor D

  field
    coneMap : ∀ {a} → ⟨ c ⇒ transport a ⟩
    coneMapCommutes : ∀ {a b} (f : ⟨ a ⇒ b ⟩) → map f ∘ coneMap ≃ coneMap

  instance
    naturalTransformation : NaturalTransformation (Δ c) D
    naturalTransformation = record
      { transform = coneMap
      ; naturality = λ f →
          begin
            coneMap ∘ id
          ≃⟨ idUnitᴿ ⟩
            coneMap
          ≃⟨ sym (coneMapCommutes _) ⟩
            map f ∘ coneMap
          ∎
      }

record Cone : Set where
  field
    apex : [ C ]
    isCone : IsCone apex

  open IsCone isCone public
