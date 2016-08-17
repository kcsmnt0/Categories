{-# OPTIONS --type-in-type #-}

module Cat.Categories.Category where

open import Cat.Category
open import Cat.Functor
open import Cat.Setoid renaming (Setoid to S)

open import Cat.Functors.Compose
open import Cat.Endofunctors.Identity

open Category {{…}}
open Functor

functorCong : ∀ {{C D E}} {F G : Functor C D} → {H I : Functor D E} → H ≊ I → F ≊ G → H ⊚ F ≊ I ⊚ G
functorCong {I = I} ⟦ q ⟧ ⟦ p ⟧ = ⟦ trans q (≃-map-cong I p) ⟧

instance
  categoryCategory : Category
  categoryCategory = record
    { _⇒_ = λ C D → functorSetoid {{C}} {{D}}
    ; isCategory = record
        { id = identityFunctor
        ; _∘_ = _⊚_
        ; idUnitᴸ = λ {C D F} → ⟦ ≃-map-cong F (refl {{C}}) ⟧
        ; idUnitᴿ = λ {C D F} → ⟦ ≃-map-cong F (refl {{C}}) ⟧
        ; assoc = λ {A B C D F G H} → ⟦ ≃-map-cong H (≃-map-cong G (≃-map-cong F (refl {{A}}))) ⟧
        ; cong⟨_∘_⟩ = functorCong
        }
    }
