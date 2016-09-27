module Cat.Structures.Semigroup where

open import Cat.Setoid

open import Cat.Categories.Setoid

record IsSemigroup A : Set where
  field
    append : ⟨ A ↦ A ↦ A ⟩
    cong-append : ∀ {x y z w} → A ⟪ x ≈ y ⟫ → A ⟪ z ≈ w ⟫ → A ⟪ append § x § z ≈ append § y § w ⟫
    assoc-append : ∀ {x y z} → A ⟪ append § x § (append § y § z) ≈ append § (append § x § y) § z ⟫

record Semigroup : Set where
  field
    Carrier : Setoid
    isSemigroup : IsSemigroup Carrier

  open IsSemigroup isSemigroup public
