open import Cat.Setoid

open import Data.Vec

module Cat.Categories.STLC {n} (g : Vec Setoid n) where

open import Cat.Category

open import Cat.Categories.Setoid
open import Cat.Setoids.STLC

open import Data.Fin

-- instance
--   stlcCategory : Category
--   stlcCategory = record
--     { Carrier = Setoid
--     ; _⇒_ = λ A B → termSetoid g (A ↦ B)
--     ; isCategory = record
--       { id = lam (var zero)
--       ; _∘_ = λ g f → lam {!app g (app f ?)!}
--       ; cong⟨_∘_⟩ = {!!}
--       ; idUnitᴸ = {!!}
--       ; idUnitᴿ = {!!}
--       ; assoc = {!!}
--       }
--     }
