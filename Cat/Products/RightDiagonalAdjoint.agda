open import Cat.Category

module Cat.Products.RightDiagonalAdjoint {{C}} where

open import Cat.Adjunction
open import Cat.Bifunctor
open import Cat.NaturalIsomorphism
open import Cat.Product

open import Cat.Categories.Product C C renaming (productCategory to C×C)
open import Cat.Categories.Setoid
open import Cat.Functors.Diagonal C
open import Cat.Functors.Compose {{C}} {{C×C}} {{C}}
open import Cat.Setoids.Product

open Bifunctor
open Functor
open Isomorphism
open NaturalTransformation

open Category C
open Category C×C renaming
  ( _⇒_ to _⇒ˣ_
  ; _≃_ to _≃ˣ_
  ; id to idˣ
  ; _∘_ to _∘ˣ_
  ; idUnitᴸ to idUnitᴸˣ
  ; idUnitᴿ to idUnitᴿˣ
  ; assoc to assocˣ
  ; begin_ to beginˣ_
  ; _≃⟨_⟩_ to _≃ˣ⟨_⟩_
  ; _∎ to _∎ˣ
  ; cong⟨_∘_⟩ to cong⟨_∘ˣ_⟩
  ; cong⟨_∘⟩ to cong⟨_∘ˣ⟩
  ; cong⟨∘_⟩ to cong⟨∘ˣ_⟩
  ; refl to reflˣ
  ; sym to symˣ
  ; trans to transˣ
  ; _~_ to _~ˣ_
  )

productFromRightDiagonalAdjoint : RightAdjoint diagonalFunctor → (a b : [ C ]) → Product a b
productFromRightDiagonalAdjoint adj a b = record
  { product = rightAdjoint ∙ (a , b)
  ; isProduct = record
    { fst = fst (transform counit)
    ; snd = snd (transform counit)
    ; factorProduct = λ f g → record
      { rightProductFactor = rightAdjunct $ (f , g)
      ; rightProductFactorFstCommutes = sym (fst (cancelRL adjunctionIsomorphism (f , g)))
      ; rightProductFactorSndCommutes = sym (snd (cancelRL adjunctionIsomorphism (f , g)))
      ; rightProductFactorUnique = λ {h} p q →
          begin
            h
          ≃⟨ sym idUnitᴸ ⟩
            id ∘ h
          ≃⟨ cong⟨ consistencyᴿ ∘⟩ ⟩
            (map rightAdjoint (transform counit) ∘ transform unit) ∘ h
          ≃⟨ sym assoc ⟩
            map rightAdjoint (transform counit) ∘ (transform unit ∘ h)
          ≃⟨ cong⟨∘ naturality unit _ ⟩ ⟩
            map rightAdjoint (transform counit) ∘ (map (rightAdjoint ⊚ Δ) h ∘ transform unit)
          ≃⟨ cong⟨∘ (sym idUnitᴿ) ⟩ ⟩
            map rightAdjoint (transform counit) ∘ ((map (rightAdjoint ⊚ Δ) h ∘ transform unit) ∘ id)
          ≃⟨ sym (naturalityᴿ _ _) ⟩
            map rightAdjoint (transform counit ∘ˣ (map Δ h ∘ˣ idˣ)) ∘ transform unit
          ≃⟨ cong⟨ ≃-map-cong rightAdjoint cong⟨∘ˣ idUnitᴿˣ ⟩ ∘⟩ ⟩
            map rightAdjoint (transform counit ∘ˣ map Δ h) ∘ transform unit
          ≃⟨ cong⟨ ≃-map-cong rightAdjoint (symˣ (p , q)) ∘⟩ ⟩
            map rightAdjoint (f , g) ∘ transform unit
          ∎
          
      }
    ; ≃-rightProductFactor-cong = λ p q → cong⟨ ≃-map-cong rightAdjoint (p , q) ∘⟩
    }
  }
  where open RightAdjoint adj
