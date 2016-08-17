{-# OPTIONS --type-in-type #-}

module Cat.Categories.SetCat where

open import Cat.Category
open import Cat.Setoid

open import Cat.Setoids.Function

open import Relation.Binary.PropositionalEquality

instance
  setCategory : Category
  setCategory = record
    { _⇒_ = functionSetoid
    ; isCategory = record
        { id = λ x → x
        ; _∘_ = λ g f x → g (f x)
        ; idUnitᴸ = λ _ → refl
        ; idUnitᴿ = λ _ → refl
        ; assoc = λ _ → refl
        ; cong⟨_∘_⟩ = cong⟨_∘_⟩
        }
    }
    where
      cong⟨_∘_⟩ : ∀ {A B C} {f g : A → B} {h i : B → C} → (∀ x → h x ≡ i x) → (∀ x → f x ≡ g x) → ∀ x → h (f x) ≡ i (g x)
      cong⟨ q ∘ p ⟩ x rewrite p x = q _
