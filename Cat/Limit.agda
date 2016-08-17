open import Cat.Category
open import Cat.Functor

module Cat.Limit {{I C}} (D : Functor I C) where

open import Cat.Cone D public

open Category C
open Cone

record IsLimitFactor {a b : [ C ]} (f : ∀ {c} → ⟨ b ⇒ D ∙ c ⟩) (g : ∀ {c} → ⟨ a ⇒ D ∙ c ⟩) : Set where
  field
    rightLimitFactor : ⟨ a ⇒ b ⟩

    limitFactorLeft : ∀ {c} → g {c} ≃ f ∘ rightLimitFactor
    rightLimitFactorUnique : ∀ {h : ⟨ a ⇒ b ⟩} → (∀ {c} → g {c} ≃ f ∘ h) → h ≃ rightLimitFactor

record Limit : Set where
  field
    cone : Cone
    factor : ∀ c → IsLimitFactor (coneMap cone) (coneMap c)

  open Cone cone public
