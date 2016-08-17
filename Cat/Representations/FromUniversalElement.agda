open import Cat.Category
open import Cat.Functor

open import Cat.Categories.Setoid

module Cat.Representations.FromUniversalElement {{C}} (F : Functor C setoidCategory) where

open import Cat.Isomorphism
open import Cat.NaturalTransformation
open import Cat.Setoid

open import Cat.Functors.Hom
open import Cat.NaturalIsomorphisms.Yoneda F
open import Cat.Representable F
open import Cat.UniversalElement F

open NaturalTransformation

-- is this a natural isomorphism between the categories of universal elements and (F ⇔ Set) natural isomorphisms?
representationFromUniversalElement : ∀ {a} {u : ⟨ F ∙ a ⟩} → UniversalElement u → IsRepresentable a
representationFromUniversalElement ue = naturalIsomorphismFromNaturalTransformations toF toHom isIso
  where
    open UniversalElement ue
    open import Cat.NaturalIsomorphisms.FromNaturalTransformations (homFunctor _) F

    toF : NaturalTransformation (homFunctor _) F
    toF = transform (yonedaToNaturalTransformation) $ _

    toHom : NaturalTransformation F (homFunctor _)
    toHom = record
      { transform = record { _$_ = to ; cong-▸ = λ _ → toUnique _ }
      ; naturality = λ _ _ → toUnique _
      }

    isIso : ∀ {b} → IsIsomorphism (transform toF {b}) (transform toHom)
    isIso = record
      { cancelLR = λ _ → toUniversal _
      ; cancelRL = λ _ → toUnique _
      }
