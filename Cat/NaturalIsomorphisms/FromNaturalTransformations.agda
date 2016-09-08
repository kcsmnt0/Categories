open import Cat.Category
open import Cat.Functor
open import Cat.Isomorphism
open import Cat.NaturalIsomorphism

open NaturalTransformation

module Cat.NaturalIsomorphisms.FromNaturalTransformations
  {{C D}}
  (F G : Functor C D)
  (α : NaturalTransformation F G)
  (β : NaturalTransformation G F)
  (iso : ∀ {a} → IsIsomorphism (transform α {a}) (transform β {a}))
  where

naturalIsomorphismFromNaturalTransformations : NaturalIsomorphism F G
naturalIsomorphismFromNaturalTransformations = record
  { transformIso = record
    { right = transform α
    ; left = transform β
    ; isIsomorphism = iso
    }
  ; naturalityᴿ = naturality α
  ; naturalityᴸ = naturality β
  }
