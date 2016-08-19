module Cat.Bifunctors.Setoid.Product where

open import Cat.Bifunctor
open import Cat.Setoid

open import Cat.Categories.Setoid
open import Cat.Categories.Product setoidCategory setoidCategory
open import Cat.Setoids.Product

open Setoid

instance
  productBifunctor : Bifunctor setoidCategory setoidCategory setoidCategory
  productBifunctor = record
    { transport = λ { (A , B) → ⟪ A × B ⟫ }
    ; isFunctor = record
      { map = λ { (f , g) → record { _$_ = < f $_ , g $_ > ; cong-▸ = < cong-▸ f , cong-▸ g > } }
      ; ≃-map-id = λ { {A , B} _ → refl A , refl B }
      ; ≃-map-∘ = λ { {A , B} {C , D} {E , F} _ → refl E , refl F }
      ; ≃-map-cong = λ p → < fst p , snd p >
      }
    }
