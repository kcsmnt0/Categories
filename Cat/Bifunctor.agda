open import Cat.Category

module Cat.Bifunctor where

open import Cat.Functor

open import Cat.Categories.Product renaming (productCategory to _×_)

Bifunctor : Category → Category → Category → Set
Bifunctor A B C = Functor (A × B) C

module Bifunctor = Functor renaming
  ( transport to bitransport
  ; map to bimap
  ; ≃-map-id to ≃-bimap-id
  ; ≃-map-∘ to ≃-bimap-∘
  ; ≃-map-cong to ≃-bimap-cong
  )
