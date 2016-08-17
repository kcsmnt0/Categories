open import Cat.Category

module Cat.Isomorphism {{C}} where

open Category C

record IsIsomorphism {a b : [ C ]} (f : ⟨ a ⇒ b ⟩) (g : ⟨ b ⇒ a ⟩) : Set where
  field
    cancelLR : f ∘ g ≃ id
    cancelRL : g ∘ f ≃ id

record Isomorphism (a b : [ C ]) : Set where
  field
    -- todo: these are backwards (haha what)
    left : ⟨ a ⇒ b ⟩
    right : ⟨ b ⇒ a ⟩
    isIsomorphism : IsIsomorphism left right

infix 0 _⇔_
_⇔_ = Isomorphism
