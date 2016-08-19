open import Cat.Category
open import Cat.Functor hiding (_≊_)

module Cat.Limit {{I C}} (D : Functor I C) where

open import Cat.Cone D public

open Category C
open Cone

record IsLeftLimitFactor {a b : [ C ]} (f : ∀ {c} → ⟨ b ⇒ D ∙ c ⟩) (g : ∀ {c} → ⟨ a ⇒ D ∙ c ⟩) : Set where
  field
    rightLimitFactor : ⟨ a ⇒ b ⟩

    rightLimitFactorCommutes : ∀ {c} → g {c} ≃ f ∘ rightLimitFactor
    rightLimitFactorUnique : ∀ {h : ⟨ a ⇒ b ⟩} → (∀ {c} → g {c} ≃ f ∘ h) → h ≃ rightLimitFactor

record Limit : Set where
  open IsLeftLimitFactor

  field
    cone : Cone
    factor : ∀ c → IsLeftLimitFactor (coneMap cone) (coneMap c)

    ≃-rightLimitFactor-cong : ∀
      {apex}
      {c c′ : IsCone apex}
      (_ : ∀ {a} → IsCone.coneMap c {a} ≃ IsCone.coneMap c′ {a})
      →
      rightLimitFactor (factor record { isCone = c }) ≃ rightLimitFactor (factor record { isCone = c′ })

  open Cone cone public
