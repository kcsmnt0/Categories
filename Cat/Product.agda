open import Cat.Category

module Cat.Product {{C}} where

open import Data.Product

open Category C

record IsLeftProductFactor
    {a b c c′ : [ C ]}
    (fst : ⟨ c ⇒ a ⟩)
    (snd : ⟨ c ⇒ b ⟩)
    (fst′ : ⟨ c′ ⇒ a ⟩)
    (snd′ : ⟨ c′ ⇒ b ⟩)
    :
    Set where
  field
    rightProductFactor : ⟨ c′ ⇒ c ⟩

    rightProductFactorFstCommutes : fst′ ≃ fst ∘ rightProductFactor
    rightProductFactorSndCommutes : snd′ ≃ snd ∘ rightProductFactor
    rightProductFactorUnique : ∀ {f : ⟨ c′ ⇒ c ⟩} → fst′ ≃ fst ∘ f → snd′ ≃ snd ∘ f → f ≃ rightProductFactor

record IsProduct (a b c : [ C ]) : Set where
  open IsLeftProductFactor

  field
    fst : ⟨ c ⇒ a ⟩
    snd : ⟨ c ⇒ b ⟩

    factorProduct : ∀ {c′} (f : ⟨ c′ ⇒ a ⟩) (g : ⟨ c′ ⇒ b ⟩) → IsLeftProductFactor fst snd f g

    ≃-rightProductFactor-cong : ∀
      {c′}
      {f f′ : ⟨ c′ ⇒ a ⟩}
      {g g′ : ⟨ c′ ⇒ b ⟩}
      (_ : f ≃ f′)
      (_ : g ≃ g′)
      →
      rightProductFactor (factorProduct f g) ≃ rightProductFactor (factorProduct f′ g′)

record Product a b : Set where
  field
    product : [ C ]
    isProduct : IsProduct a b product

  open IsProduct isProduct public
