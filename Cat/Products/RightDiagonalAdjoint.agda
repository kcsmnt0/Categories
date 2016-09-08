open import Cat.Category

module Cat.Products.RightDiagonalAdjoint {{C : Category}} where

open import Cat.Adjunction
open import Cat.Bifunctor
open import Cat.NaturalTransformation
open import Cat.Product

open import Cat.Categories.Product C C
open import Cat.Functors.Diagonal C
open import Cat.Setoids.Product

open Bifunctor
open Functor
open NaturalTransformation

open Category productCategory

-- productFromRightDiagonalAdjoint : ∀ {Pair} → diagonalFunctor ⊣ Pair → ∀ a b → Product a b
-- productFromRightDiagonalAdjoint = ?
