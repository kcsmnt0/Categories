{-# OPTIONS --type-in-type #-}

module Cat.Setoids.FreeSemigroup where

open import Cat.Setoid

data FreeSemigroup (A : Setoid) : Set where
  [_] : ⟨ A ⟩ → FreeSemigroup A
  _⊕_ : FreeSemigroup A → FreeSemigroup A → FreeSemigroup A

data _≊_ {A} : FreeSemigroup A → FreeSemigroup A → Set where
  [_] : ∀ {x y} → A ⟪ x ≈ y ⟫ → [ x ] ≊ [ y ]
  _⊕_ : ∀ {x y z w} → x ≊ y → z ≊ w → (x ⊕ z) ≊ (y ⊕ w)
