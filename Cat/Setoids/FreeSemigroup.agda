{-# OPTIONS --type-in-type #-}

module Cat.Setoids.FreeSemigroup where

open import Cat.Setoid

infixr 4 _⊕_
data FreeSemigroup (A : Setoid) : Set where
  [_] : ⟨ A ⟩ → FreeSemigroup A
  _⊕_ : FreeSemigroup A → FreeSemigroup A → FreeSemigroup A

infix 2 _≊_
data _≊_ {A} : FreeSemigroup A → FreeSemigroup A → Set where
  [_] : ∀ {x y} → A ⟪ x ≈ y ⟫ → [ x ] ≊ [ y ]
  ≊-cong⟨_⊕_⟩ : ∀ {x y z w} → x ≊ y → z ≊ w → (x ⊕ z) ≊ (y ⊕ w)
  ≊-assoc-⊕ : ∀ {x y z} → x ⊕ (y ⊕ z) ≊ (x ⊕ y) ⊕ z
