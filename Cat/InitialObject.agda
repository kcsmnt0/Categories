module Cat.InitialObject {{C}} where

open import Cat.Category
open import Cat.Isomorphism
open import Cat.Setoid

open Category C

record IsInitialObject (a : [ C ]) : Set where
  field
    from : ∀ {x} → ⟨ a ⇒ x ⟩
    fromUnique : ∀ {x} → IsUnique (a ⇒ x) from

record InitialObject : Set where
  field
    origin : [ C ]
    isInitialObject : IsInitialObject origin

  open IsInitialObject isInitialObject public

open InitialObject

initialObjectUnique : ∀ a b → origin a ⇔ origin b
initialObjectUnique a b = record
  { left = from a
  ; right = from b
  ; isIsomorphism = record
    { cancelLR =
        begin
          from a ∘ from b
        ≃⟨ sym (fromUnique b) ⟩
          from b
        ≃⟨ fromUnique b ⟩
          id
        ∎
    ; cancelRL =
        begin
          from b ∘ from a
        ≃⟨ sym (fromUnique a) ⟩
          from a
        ≃⟨ fromUnique a ⟩
          id
        ∎
    }
  }
