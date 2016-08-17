open import Cat.Functor
open import Cat.Limit

module Cat.TerminalObjects.Cone.Limit {{I C}} {D : Functor I C} (L : Limit D) where

open import Cat.Category
open import Cat.TerminalObject

open import Cat.Categories.Cone D

open Category C
open Limit L

instance
  terminalObjectLimit : TerminalObject {{coneCategory}}
  terminalObjectLimit = record
    { terminus = cone
    ; isTerminalObject = record
      { to = λ {c} → let open IsLimitFactor (factor c) in record
        { factorApex = rightLimitFactor
        ; factorApexCommutes = limitFactorLeft
        }
      ; toUnique = λ {c}{f} →
          let
            open _▸_ f
            open IsLimitFactor (factor c)
          in
            sym (rightLimitFactorUnique factorApexCommutes)
      }
    }
