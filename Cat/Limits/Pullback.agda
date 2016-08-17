open import Cat.Category
open import Cat.Functor

open import Cat.Quivers.Pullback
open import Cat.Categories.Free _▸_ renaming (freeCategory to I)

module Cat.Limits.Pullback {{C : Category}} (D : Functor I C) where

open import Cat.Limit

Pullback : Set
Pullback = Limit D
