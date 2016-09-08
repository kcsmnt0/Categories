open import Cat.Category

module Cat.Bifunctor where

open import Cat.Functor public

open import Cat.Categories.Product renaming (productCategory to _×_)
open import Cat.Categories.Setoid

Bifunctor : Category → Category → Category → Set
Bifunctor A B C = Functor (A × B) C

module Bifunctor = Functor renaming
  ( transport to bitransport
  ; map to bimap
  ; ≃-map-id to ≃-bimap-id
  ; ≃-map-∘ to ≃-bimap-∘
  ; ≃-map-cong to ≃-bimap-cong
  )

Profunctor : Category → Category → Set
Profunctor C D = Bifunctor (Category.op C) D setoidCategory
