open import Cat.Category
open import Cat.Functor

open import Cat.Categories.Setoid

module Cat.NaturalIsomorphisms.Yoneda {{C}} (F : Functor C setoidCategory) where

open import Cat.NaturalIsomorphism
open import Cat.Setoid renaming (module Setoid to S)

open import Cat.Functors.FunctorApply C setoidCategory
open import Cat.Functors.Yoneda F
open import Cat.Setoids.Product

open Category C
open Functor
open NaturalTransformation

instance
  yonedaNaturalIsomorphism : NaturalIsomorphism yonedaFunctor functorApplyFunctor
  yonedaNaturalIsomorphism = record
    { transformIso = λ { {F , a} → record
      { right = record { _$_ = λ α → transform α $ id ; cong-▸ = λ p → p _ } 
      ; left = record
        { _$_ = λ x → record
          { transform = record { _$_ = λ g → map F g $ x ; cong-▸ = λ p → ≃-map-cong F p x }
          ; naturality = λ f g → S.sym (F ∙ _) (≃-map-∘ F x)
          }
        ; cong-▸ = λ p f → cong-▸ (map F f) p
        }
      ; isIsomorphism = record
        { cancelLR = λ x → ≃-map-id F x
        ; cancelRL = λ α f → S.trans (F ∙ _) (S.sym (F ∙ _) (naturality α f id)) (cong-▸ (transform α) idUnitᴿ)
        }
      } }
    ; naturalityᴿ = λ { {F , a}  {G , b} (α , f) β →
        cong-▸ (transform α)
            (S.trans (F ∙ _) (cong-▸ (transform β) (trans idUnitᴸ (sym idUnitᴿ))) (naturality β f id)) }
    ; naturalityᴸ = λ { {F , a} {G , b} (α , f) x g →
        S.trans (G ∙ _)
        (S.sym (G ∙ _) (naturality α g (map F f $ x)))
        (cong-▸ (transform α) (≃-map-∘ F _)) }
    }

open NaturalIsomorphism yonedaNaturalIsomorphism public using () renaming
  ( leftNaturalTransformation to yonedaToAppliedFunctor
  ; rightNaturalTransformation to yonedaToNaturalTransformation
  ) public
