{-# OPTIONS --type-in-type #-}

open import Cat.Category
open import Cat.Limit

open import Cat.Quivers.Product
import Cat.Functors.FromQuiver as FunctorFromQuiver

module Cat.Limits.Product
  {{C}}
  {a b : [ C ]}
  (l : let open FunctorFromQuiver _▸_ {transport a b} map in Limit functorFromQuiver)
  where

open import Cat.Functor
open import Cat.Product

open FunctorFromQuiver _▸_ {transport a b} map

open Limit l

open import Cat.Cones.FromQuiver _▸_ {transport a b} map

productLimit : Product a b
productLimit = record
  { product = apex
  ; isProduct = record
      { fst = coneMap {α}
      ; snd = coneMap {β}
      ; factorProduct = λ f g →
          let
            open IsLeftLimitFactor (factor (coneFromQuiver _ (λ { {α} → f ; {β} → g }) (λ ())))
          in
            record
              { rightProductFactor = rightLimitFactor
              ; rightProductFactorFstCommutes = rightLimitFactorCommutes
              ; rightProductFactorSndCommutes = rightLimitFactorCommutes
              ; rightProductFactorUnique = λ p q → rightLimitFactorUnique λ { {α} → p ; {β} → q }
              }
      ; ≃-rightProductFactor-cong = λ p q → ≃-rightLimitFactor-cong λ { {α} → p ; {β} → q }
      }
  }
