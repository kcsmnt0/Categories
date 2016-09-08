{-# OPTIONS --type-in-type #-}

open import Cat.Category

module Cat.Functors.Hom where

open import Cat.Bifunctor
open import Cat.Functor
open import Cat.Setoid

open import Cat.Categories.Setoid
open import Cat.Endofunctors.Identity
open import Cat.Functors.Compose
open import Cat.Functors.FromBifunctor
open import Cat.Functors.Product
open import Cat.Setoids.Product

open Category {{…}}
open Functor

homProfunctorUnderFunctors : ∀ {{A B C}} → Functor A C → Functor B C → Profunctor A B
homProfunctorUnderFunctors F G = record
  { transport = λ { (a , b) → F ∙ a ⇒ G ∙ b }
  ; isFunctor = record
    { map = λ { (f , g) → record
      { _$_ = λ h → map G g ∘ h ∘ map F f
      ; cong-▸ = λ p → cong⟨∘ cong⟨ p ∘⟩ ⟩ }
      }
    ; ≃-map-id = λ f →
        begin
          map G id ∘ f ∘ map F id
        ≃⟨ cong⟨ ≃-map-id G ∘⟩ ⟩
          id ∘ f ∘ map F id
        ≃⟨ idUnitᴸ ⟩
          f ∘ map F id
        ≃⟨ cong⟨∘ ≃-map-id F ⟩ ⟩
          f ∘ id
        ≃⟨ idUnitᴿ ⟩
          f
        ∎
    ; ≃-map-∘ = λ { {_}{_}{_} {f , g} {h , i} j →
        begin
          map G i ∘ ((map G g ∘ (j ∘ map F f)) ∘ map F h)
        ≃⟨ cong⟨∘ cong⟨ assoc ∘⟩ ⟩ ⟩
          map G i ∘ (((map G g ∘ j) ∘ map F f) ∘ map F h)
        ≃⟨ cong⟨∘ sym assoc ⟩ ⟩
          map G i ∘ ((map G g ∘ j) ∘ (map F f ∘ map F h))
        ≃⟨ assoc ⟩
          (map G i ∘ (map G g ∘ j)) ∘ (map F f ∘ map F h)
        ≃⟨ cong⟨ assoc ∘⟩ ⟩
          ((map G i ∘ map G g) ∘ j) ∘ (map F f ∘ map F h)
        ≃⟨ cong⟨ cong⟨ (≃-map-∘ G) ∘⟩ ∘⟩ ⟩
          (map G (i ∘ g) ∘ j) ∘ (map F f ∘ map F h)
        ≃⟨ cong⟨∘ ≃-map-∘ F ⟩ ⟩
          (map G (i ∘ g) ∘ j) ∘ map F (f ∘ h)
        ≃⟨ sym assoc ⟩
          map G (i ∘ g) ∘ (j ∘ map F (f ∘ h))
        ∎ }
    ; ≃-map-cong = λ { (p , q) _ → cong⟨ ≃-map-cong G q ∘ cong⟨∘ ≃-map-cong F p ⟩ ⟩ }
    }
  }

homProfunctor : ∀ {{C}} → Profunctor C C
homProfunctor = homProfunctorUnderFunctors identityFunctor identityFunctor

homFunctor : ∀ {{C}} → [ C ] → Functor C setoidCategory
homFunctor = sndFunctor {{_}} homProfunctor -- weird

homContrafunctor : ∀ {{C}} → [ C ] → Contrafunctor C setoidCategory
homContrafunctor = fstFunctor homProfunctor
