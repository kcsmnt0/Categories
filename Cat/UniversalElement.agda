open import Cat.Category
open import Cat.Functor

open import Cat.Categories.Setoid

module Cat.UniversalElement {{C}} (F : Functor C setoidCategory) where

open import Cat.Setoid

open Category C
open Functor F

record UniversalElement {a : [ C ]} (u : ⟨ F ∙ a ⟩) : Set where
  field
    to : ∀ {b} (v : ⟨ F ∙ b ⟩) → ⟨ a ⇒ b ⟩
    toUnique : ∀ {b} (v : ⟨ F ∙ b ⟩) → IsUnique (a ⇒ b) (to v)
    toUniversal : ∀ {b} (v : ⟨ F ∙ b ⟩) → transport b ⟪ (map (to v) $ u) ≈ v ⟫
