{-# OPTIONS --type-in-type #-}

module Cat.Setoids.Pi where

open import Cat.Isomorphism
open import Cat.Setoid

open import Cat.Categories.Setoid
open import Cat.Setoids.Setoid

open Setoid

Π_ : ∀ {A} → (A ▸ setoidSetoid) → Setoid
Π_ {A} B = record
  { Carrier = ∀ x → ⟨ B $ x ⟩
  ; _≈_ = λ f g → ∀ x → (B $ x) ⟪ f x ≈ g x ⟫
  ; isEquivalence = record
    { refl = λ x → refl (B $ x)
    ; sym = λ p x → sym (B $ x) (p x)
    ; trans = λ p q x → trans (B $ x) (p x) (q x)
    }
  }
