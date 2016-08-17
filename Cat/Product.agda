open import Cat.Category

module Cat.Product {{C}} (a b : [ C ]) where

open import Data.Product

open Category C

record IsProductFactor
    {c c′ : [ C ]}
    (fst : ⟨ c ⇒ a ⟩)
    (snd : ⟨ c ⇒ b ⟩)
    (fst′ : ⟨ c′ ⇒ a ⟩)
    (snd′ : ⟨ c′ ⇒ b ⟩)
    :
    Set where
  field
    leftProductFactor : ⟨ c′ ⇒ c ⟩

    productFactorLeftFst : fst′ ≃ fst ∘ leftProductFactor
    productFactorLeftSnd : snd′ ≃ snd ∘ leftProductFactor
    leftProductFactorUnique : ∀ {f : ⟨ c′ ⇒ c ⟩} → fst′ ≃ fst ∘ f → snd′ ≃ snd ∘ f → f ≃ leftProductFactor

record IsProduct (c : [ C ]) : Set where
  field
    fst : ⟨ c ⇒ a ⟩
    snd : ⟨ c ⇒ b ⟩
    factorProduct : ∀ {c′} (f : ⟨ c′ ⇒ a ⟩) (g : ⟨ c′ ⇒ b ⟩) → IsProductFactor fst snd f g

record Product : Set where
  field
    product : [ C ]
    isProduct : IsProduct product
