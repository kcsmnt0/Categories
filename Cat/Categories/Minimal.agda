{-# OPTIONS --type-in-type #-}

-- the smallest category around a given set of objects, where the only morphisms are identities
module Cat.Categories.Minimal A where

open import Cat.Category
open import Cat.Setoid

open import Cat.Setoids.SetSetoid

open import Relation.Binary.PropositionalEquality

reflUnitᴸ : {a b : A} {p : a ≡ b} → trans p refl ≡ p
reflUnitᴸ {p = refl} = refl

reflUnitᴿ : {a b : A} {p : a ≡ b} → trans refl p ≡ p
reflUnitᴿ {p = refl} = refl

≡-assoc : {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) → trans (trans p q) r ≡ trans p (trans q r)
≡-assoc refl _ _ = refl

≡-cong⟨_∘_⟩ : {a b c : A} {f g : a ≡ b} {h i : b ≡ c} → h ≡ i → f ≡ g → trans f h ≡ trans g i
≡-cong⟨ refl ∘ refl ⟩ = refl

instance
  minimalCategory : Category
  minimalCategory = record
    { Carrier = A
    ; _⇒_ = λ i j → setSetoid (i ≡ j)
    ; isCategory = record
        { id = refl
        ; _∘_ = λ q p → trans p q
        ; idUnitᴸ = reflUnitᴸ
        ; idUnitᴿ = reflUnitᴿ
        ; assoc = λ { {g = g} {h} {i} → ≡-assoc g h i }
        ; cong⟨_∘_⟩ = ≡-cong⟨_∘_⟩
        }
    }
