open import Cat.Category
open import Cat.Functor

module Cat.NaturalTransformation {{C D}} (F G : Functor C D) where

open import Cat.Setoid

open Category {{…}}
open Functor

Naturality : (α : ∀ {a} → ⟨ F ∙ a ⇒ G ∙ a ⟩) → Set
Naturality α = {a b : [ C ]} (f : ⟨ a ⇒ b ⟩) → α ∘ map F f ≃ map G f ∘ α

record NaturalTransformation : Set where
  field
    transform : ∀ {a} → ⟨ F ∙ a ⇒ G ∙ a ⟩
    naturality : Naturality transform

open NaturalTransformation

_≈_ : NaturalTransformation → NaturalTransformation → Set
α ≈ β = ∀ {a} → transform α {a} ≃ transform β {a}

instance
  naturalTransformationSetoid : Setoid
  naturalTransformationSetoid = record
    { Carrier = NaturalTransformation
    ; _≈_ = _≈_
    ; isEquivalence = record
      { refl = refl
      ; sym = λ p → sym p
      ; trans = λ p q → trans p q
      }
    }
