{-# OPTIONS --type-in-type #-}

module Cat.InitialObjects.SetCat.Bot where

open import Cat.Category
open import Cat.InitialObject

open import Cat.Categories.SetCat

open import Data.Empty

instance
  emptyInitialObject : InitialObject
  emptyInitialObject = record
    { origin = ⊥
    ; isInitialObject = record
      { from = λ ()
      ; fromUnique = λ ()
      }
    }
