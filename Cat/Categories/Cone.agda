{-# OPTIONS --type-in-type #-}

open import Cat.Category
open import Cat.Functor

module Cat.Categories.Cone {{I C}} (F : Functor I C) where

open import Cat.Cone F
open import Cat.Setoid

open Category C
open Cone

record _▸_ (D E : Cone) : Set where
  field
    factorApex : ⟨ apex D ⇒ apex E ⟩
    factorApexCommutes : ∀ {a} → coneMap D {a} ≃ coneMap E ∘ factorApex

open _▸_

_↦_ : Cone → Cone → Setoid
a ↦ b = record
  { Carrier = a ▸ b
  ; _≈_ = λ f g → factorApex f ≃ factorApex g
  ; isEquivalence = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  }

cone-id : ∀ {a} → a ▸ a
cone-id = record { factorApex = id ; factorApexCommutes = sym idUnitᴿ }

cone-∘ : ∀ {a b c} → b ▸ c → a ▸ b → a ▸ c
cone-∘ {a = a} {b} {c} g f = record
  { factorApex = factorApex g ∘ factorApex f
  ; factorApexCommutes =
      begin
        coneMap a
      ≃⟨ factorApexCommutes f ⟩
        coneMap b ∘ factorApex f
      ≃⟨ cong⟨ factorApexCommutes g ∘⟩ ⟩
        (coneMap c ∘ factorApex g) ∘ factorApex f
      ≃⟨ sym assoc ⟩
        coneMap c ∘ (factorApex g ∘ factorApex f)
      ∎
  }

instance
  coneCategory : Category
  coneCategory = record
    { _⇒_ = _↦_
    ; isCategory = record
        { id = cone-id
        ; _∘_ = cone-∘
        ; cong⟨_∘_⟩ = cong⟨_∘_⟩
        ; idUnitᴸ = idUnitᴸ
        ; idUnitᴿ = idUnitᴿ
        ; assoc = assoc
        }
    }
