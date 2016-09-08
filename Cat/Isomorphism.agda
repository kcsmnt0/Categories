open import Cat.Category

module Cat.Isomorphism {{C}} where

open Category C

record IsIsomorphism {a b : [ C ]} (f : ⟨ a ⇒ b ⟩) (g : ⟨ b ⇒ a ⟩) : Set where
  field
    cancelLR : f ∘ g ≃ id
    cancelRL : g ∘ f ≃ id

record Isomorphism (a b : [ C ]) : Set where
  field
    right : ⟨ a ⇒ b ⟩
    left : ⟨ b ⇒ a ⟩
    isIsomorphism : IsIsomorphism right left

  open IsIsomorphism isIsomorphism public

infix 0 _⇔_
_⇔_ = Isomorphism
