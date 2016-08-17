open import Cat.Category
open import Cat.Functor
open import Cat.NaturalTransformation

open import Cat.Functors.Constant

module Cat.Cones.FromNaturalTransformation
  {{C D}}
  (a : [ D ])
  (F : Functor C D)
  (α : NaturalTransformation (Δ a) F)
  where

open import Cat.Cone

open Category D
open NaturalTransformation

instance
  fromConstantFunctorCone : Cone F
  fromConstantFunctorCone = record
    { apex = a
    ; isCone = record
        { coneMap = transform α
        ; coneMapCommutes = λ f → trans (sym (naturality α f)) idUnitᴿ
        }
    }
