open import Cat.Category
open import Cat.Functor

module Cat.NaturalIsomorphism {{C D}} (F G : Functor C D) where

open import Cat.Isomorphism
open import Cat.NaturalTransformation public
open import Cat.Setoid

open Isomorphism

record NaturalIsomorphism : Set where
  field
    transform : {a : [ C ]} → F ∙ a ⇔ G ∙ a
    naturalityᴸ : Naturality F G (left transform)
    naturalityᴿ : Naturality G F (right transform)

  leftNaturalTransformation : NaturalTransformation F G
  leftNaturalTransformation = record { naturality = naturalityᴸ }

  rightNaturalTransformation : NaturalTransformation G F
  rightNaturalTransformation = record { naturality = naturalityᴿ }
