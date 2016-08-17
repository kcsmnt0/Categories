{-# OPTIONS --type-in-type #-}

module Cat.TerminalObjects.SetCat.Unit where

open import Cat.Category
open import Cat.TerminalObject

open import Cat.Categories.SetCat

open import Data.Unit
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

unitUnique : {x y : ⊤} → x ≡ y
unitUnique {tt} {tt} = PE.refl

instance
  unitTerminalObject : TerminalObject
  unitTerminalObject = record
    { terminus = ⊤
    ; isTerminalObject = record
      { to = λ _ → tt
      ; toUnique = λ _ → unitUnique
      }
    }
