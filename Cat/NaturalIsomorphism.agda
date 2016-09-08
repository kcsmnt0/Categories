open import Cat.Category
open import Cat.Functor

module Cat.NaturalIsomorphism {{C D}} (F G : Functor C D) where

open import Cat.Isomorphism public
open import Cat.NaturalTransformation public
open import Cat.Setoid

record NaturalIsomorphism : Set where
  field
    transformIso : {a : [ C ]} → F ∙ a ⇔ G ∙ a
    naturalityᴿ : Naturality F G (Isomorphism.right transformIso)
    naturalityᴸ : Naturality G F (Isomorphism.left transformIso)

  leftNaturalTransformation : NaturalTransformation F G
  leftNaturalTransformation = record { naturality = naturalityᴿ }

  rightNaturalTransformation : NaturalTransformation G F
  rightNaturalTransformation = record { naturality = naturalityᴸ }
