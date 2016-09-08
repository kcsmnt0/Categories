open import Cat.Category
open import Cat.Functor

open import Cat.Categories.Setoid

-- the left side of the Yoneda lemma's natural isomorphism:
-- takes an object a to the set of natural transformations from Hom a to F a
module Cat.Functors.Yoneda {{C}} (F : Functor C setoidCategory) where

open import Cat.NaturalTransformation
open import Cat.Setoid renaming (module Setoid to S)

open import Cat.Categories.Functor C setoidCategory
open import Cat.Categories.Product functorCategory C
open import Cat.Functors.Hom
open import Cat.Setoids.Product

open Functor
open NaturalTransformation

instance
  -- i think this should be able to be at most half as ugly
  yonedaFunctor : Functor productCategory setoidCategory
  yonedaFunctor = record
    { transport = λ { (F , a) → naturalTransformationSetoid {{C}} {{setoidCategory}} {homFunctor a} {F} }
    ; isFunctor = record
      { map = λ { {_} {G , b} (α , f) → record
        { _$_ = λ β → record
          { transform = λ {x} →
              let open Category setoidCategory in
                transform α ∘ transform β ∘ map (homContrafunctor x) f
          ; naturality = λ {x y} g h →
              let open Category C in
                S.trans (G ∙ y)
                  (cong-▸ (transform α) (cong-▸ (transform β) (sym assoc)))
                  (S.trans (G ∙ y)
                    (cong-▸ (transform α) (naturality β g (h ∘ f)))
                    (naturality α g (transform β $ (h ∘ f))))
          }
        ; cong-▸ = let open Category C in λ p h → cong-▸ (transform α) (p (h ∘ f)) }
        }
      ; ≃-map-id = let open Category C in λ β _ → cong-▸ (transform β) idUnitᴿ
      ; ≃-map-∘ = λ { {F , a} {G , b} {H , c} {β , g} {α , h} γ _ →
          let open Category C in
            cong-▸ (transform α) (cong-▸ (transform β) (cong-▸ (transform γ) (sym assoc))) }
      ; ≃-map-cong = λ
          { {F , a} {G , b} {α , f} {β , g} (p , q) γ {x} h → let open Category C in
              S.trans (G ∙ x)
                (p _)
                (cong-▸ (transform β) (cong-▸ (transform γ) cong⟨∘ q ⟩)) }
      }
    }
