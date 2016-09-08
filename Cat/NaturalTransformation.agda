open import Cat.Category

module Cat.NaturalTransformation {{C D : Category}} where

open import Cat.Functor
open import Cat.Setoid

open Category {{…}}
open Functor

Naturality : (F G : Functor C D) → (α : ∀ {a} → ⟨ F ∙ a ⇒ G ∙ a ⟩) → Set
Naturality F G α = {a b : [ C ]} (f : ⟨ a ⇒ b ⟩) → α ∘ map F f ≃ map G f ∘ α

record NaturalTransformation (F G : Functor C D) : Set where
  field
    transform : ∀ {a} → ⟨ F ∙ a ⇒ G ∙ a ⟩
    naturality : Naturality F G transform

open NaturalTransformation

_≈_ : ∀ {F G} → NaturalTransformation F G → NaturalTransformation F G → Set
α ≈ β = ∀ {a} → transform α {a} ≃ transform β {a}

instance
  naturalTransformationSetoid : ∀ {F G} → Setoid
  naturalTransformationSetoid {F} {G} = record
    { Carrier = NaturalTransformation F G
    ; _≈_ = _≈_
    ; isEquivalence = record
      { refl = refl
      ; sym = λ p → sym p
      ; trans = λ p q → trans p q
      }
    }
