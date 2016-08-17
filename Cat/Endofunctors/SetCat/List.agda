{-# OPTIONS --type-in-type #-}

module Cat.Endofunctors.SetCat.List where

open import Cat.Category
open import Cat.Functor

open import Cat.Categories.SetCat

open import Data.List as List
open import Relation.Binary.PropositionalEquality as PE

open Category setCategory

≡-map-id : ∀ {A} (xs : List A) → map id xs ≡ xs
≡-map-id [] = PE.refl
≡-map-id (x ∷ xs) = cong (x ∷_) (≡-map-id xs)

≡-map-∘ : ∀ {A B C} {f : A → B} {g : B → C} (xs : List A) → map g (map f xs) ≡ map (g ∘ f) xs
≡-map-∘ [] = PE.refl
≡-map-∘ (x ∷ xs) = cong (_ ∷_) (≡-map-∘ xs)

≡-map-cong : ∀ {A B} {f g : A → B} → f ≃ g → (xs : List A) → map f xs ≡ map g xs
≡-map-cong p [] = PE.refl
≡-map-cong p (x ∷ xs) = cong₂ _∷_ (p x) (≡-map-cong p xs)

instance
  listFunctor : Endofunctor setCategory
  listFunctor = record
    { isFunctor = record
      { map = map
      ; ≃-map-id = ≡-map-id
      ; ≃-map-∘ = ≡-map-∘
      ; ≃-map-cong = ≡-map-cong
      }
    }
