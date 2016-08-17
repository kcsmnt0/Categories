{-# OPTIONS --type-in-type #-}

module Cat.Setoid where

open import Relation.Binary.PropositionalEquality as PE using (_≡_)

record IsEquivalence {A} (_≈_ : A → A → Set) : Set where
  field
    refl : ∀ {a} → a ≈ a
    sym : ∀ {a b} → a ≈ b → b ≈ a
    trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c

record Setoid : Set where
  infix 4 _≈_

  field
    {Carrier} : Set
    _≈_ : Carrier → Carrier → Set
    instance isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

open Setoid

⟨_⟩ : Setoid → Set
⟨_⟩ = Carrier

_⟪_≈_⟫ : ∀ A → ⟨ A ⟩ → ⟨ A ⟩ → Set
A ⟪ x ≈ y ⟫ = _≈_ A x y

≡-to-≈ : ∀ A {a b : ⟨ A ⟩} → a ≡ b → A ⟪ a ≈ b ⟫
≡-to-≈ A PE.refl = refl A

IsUnique : ∀ A → ⟨ A ⟩ → Set
IsUnique A x = ∀ {y} → A ⟪ x ≈ y ⟫

record Unique A : Set where
  field
    element : ⟨ A ⟩
    isUnique : IsUnique A element
