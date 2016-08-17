open import Cat.Category
open import Cat.Functor

module Cat.Adjunction {{C D}} (F : Functor C D) (G : Functor D C) where

open import Cat.NaturalTransformation

open import Cat.Categories.Category

open Category categoryCategory


record Adjunction : Set where
  field
    unit : NaturalTransformation id (F ∘ G)
    counit : NaturalTransformation (G ∘ F) id
    rightConsistency : F ≃ F ∘ G ∘ F
    leftConsistency : G ≃ G ∘ F ∘ G

_⊣_ = Adjunction
