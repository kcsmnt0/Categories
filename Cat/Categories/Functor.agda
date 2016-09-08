{-# OPTIONS --type-in-type #-}

open import Cat.Category

module Cat.Categories.Functor (C D : Category) where

open import Cat.Functor
open import Cat.NaturalTransformation

open import Cat.NaturalTransformations.Identity
open import Cat.NaturalTransformations.Compose

open Category D

instance
  functorCategory : Category
  functorCategory = record
    { Carrier = Functor C D
    ; _⇒_ = λ F G → naturalTransformationSetoid {F} {G}
    ; isCategory = record
        { id = identityNaturalTransformation _
        ; _∘_ = _⊚_
        ; idUnitᴸ = idUnitᴸ
        ; idUnitᴿ = idUnitᴿ
        ; assoc = assoc
        ; cong⟨_∘_⟩ = λ q p → cong⟨ q ∘ p ⟩
        }
    }
