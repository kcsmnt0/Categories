{-# OPTIONS --type-in-type #-}

module Cat.Categories.Monoid where

open import Cat.Category
open import Cat.Setoid

open import Cat.Categories.Setoid

record Monoid : Set where
  field
    {Carrier} : Setoid
    _⊕_ : ⟨ Carrier ⟩ → ⟨ Carrier ⟩ → ⟨ Carrier ⟩
    neutral : ⟨ Carrier ⟩

  open Setoid Carrier

  field
    assoc : ∀ {a b c} → a ⊕ (b ⊕ c) ≈ (a ⊕ b) ⊕ c
    neutralUnitᴸ : ∀ {a} → neutral ⊕ a ≈ a
    neutralUnitᴿ : ∀ {a} → a ⊕ neutral ≈ a
    cong⟨_⊕_⟩ : ∀ {a b c d} → a ≈ b → c ≈ d → a ⊕ c ≈ b ⊕ d

open Monoid

_▹_ : Monoid → Monoid → Setoid
A ▹ B = let open Setoid (Carrier B) hiding (Carrier) in record
  { Carrier = Carrier A ▸ Carrier B
  ; _≈_ = λ f g → ∀ x → (f $ x) ≈ (g $ x)
  ; isEquivalence = record
    { refl = λ _ → refl
    ; sym = λ p x → sym (p x)
    ; trans = λ p q x → trans (p x) (q x)
    }
  }

open Setoid hiding (Carrier)

instance
  monoidCategory : Category
  monoidCategory = record
    { _⇒_ = _▹_
    ; isCategory = record
      { id = record { _$_ = λ x → x ; cong-▸ = λ p → p }
      ; _∘_ = λ g f → record { _$_ = λ x → g $ f $ x ; cong-▸ = λ p → cong-▸ g (cong-▸ f p) }
      ; cong⟨_∘_⟩ = λ { {c = c} {h = h} q p x → trans (Carrier c) (cong-▸ h (p x)) (q _) }
      ; idUnitᴸ = λ { {a} {_} {f} x → cong-▸ f (refl (Carrier a)) }
      ; idUnitᴿ = λ { {a} {_} {f} x → cong-▸ f (refl (Carrier a)) }
      ; assoc = λ { {d = d} _ → refl (Carrier d) }
      }
    }
