module Cat.TerminalObject {{C}} where

open import Cat.Category
open import Cat.Isomorphism
open import Cat.Setoid

open Category C

record IsTerminalObject (a : [ C ]) : Set where
  field
    to : ∀ {x} → ⟨ x ⇒ a ⟩
    toUnique : ∀ {x} → IsUnique (x ⇒ a) (to {x})

record TerminalObject : Set where
  field
    terminus : [ C ]
    isTerminalObject : IsTerminalObject terminus

  open IsTerminalObject isTerminalObject public

open TerminalObject

terminalObjectUnique : (a b : TerminalObject) → terminus a ⇔ terminus b
terminalObjectUnique a b = record
  { right = to b
  ; left = to a
  ; isIsomorphism = record
    { cancelLR =
        begin
          to b ∘ to a
        ≃⟨ sym (toUnique b) ⟩
          to b
        ≃⟨ toUnique b ⟩
          id
        ∎
    ; cancelRL =
        begin
          to a ∘ to b
        ≃⟨ sym (toUnique a) ⟩
          to a
        ≃⟨ toUnique a ⟩
          id
        ∎
    }
  }
