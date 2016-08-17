{-# OPTIONS --type-in-type #-}

module Cat.Functors.SetToSetoid where

open import Cat.Category
open import Cat.Functor
open import Cat.Setoid

open import Cat.Categories.SetCat
open import Cat.Categories.Setoid
open import Cat.Setoids.SetSetoid

open import Relation.Binary.PropositionalEquality

setToSetoidFunctor : Functor setCategory setoidCategory
setToSetoidFunctor = record
  { transport = setSetoid
  ; isFunctor = record
    { map = λ f → record { _$_ = f ; cong-▸ = λ { {_}.{_} refl → refl } }
    ; ≃-map-id = λ _ → refl
    ; ≃-map-∘ = λ _ → refl
    ; ≃-map-cong = λ p → p
    }
  }
