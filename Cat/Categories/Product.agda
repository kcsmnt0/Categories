{-# OPTIONS --type-in-type #-}

module Cat.Categories.Product C D where

open import Cat.Category
open import Cat.Setoid

open import Cat.Setoids.Product

open Category

_⇉_ : [ C ] × [ D ] → [ C ] × [ D ] → Setoid
(a , b) ⇉ (c , d) = record
  { Carrier = ⟨ _⇒_ C a c ⟩ × ⟨ _⇒_ D b d ⟩
  ; _≈_ = λ { (f , g) (h , i) → _≃_ C f h × _≃_ D g i }
  ; isEquivalence = record
    { refl = refl C , refl D
    ; sym = < sym C , sym D >
    ; trans = < trans C ,, trans D >
    }
  }

instance
  productCategory : Category
  productCategory = record
    { _⇒_ = _⇉_
    ; isCategory = record
        { id = id C , id D
        ; _∘_ = < _∘_ C ,, _∘_ D >
        ; cong⟨_∘_⟩ = < cong⟨_∘_⟩ C ,, cong⟨_∘_⟩ D >
        ; idUnitᴸ = idUnitᴸ C , idUnitᴸ D
        ; idUnitᴿ = idUnitᴿ C , idUnitᴿ D
        ; assoc = assoc C , assoc D
        }
    }
