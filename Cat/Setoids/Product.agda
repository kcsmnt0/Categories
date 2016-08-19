{-# OPTIONS --type-in-type #-}

module Cat.Setoids.Product where

open import Cat.Setoid

open Setoid

infixr 2 _×_ _,_
record _×_ A B : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

infix 2 <_,_>
<_,_> : ∀
  {A B : Set}
  {C : A → Set} {D : B → Set}
  (f : ∀ x → C x) (g : ∀ y → D y)
  (pr : A × B)
  →
  (C (fst pr) × D (snd pr))
< f , g > (x , y) = f x , g y

<_,,_> : ∀
  {A B : Set}
  {C : A → Set} {D : B → Set}
  {E : ∀ {x} → C x → Set} {F : ∀ {y} → D y → Set}
  (f : ∀ x (z : C x) → E z) (g : ∀ y (w : D y) → F w)
  (pr₁ : A × B)
  (pr₂ : C (fst pr₁) × D (snd pr₁))
  →
  (E (fst pr₂) × F (snd pr₂))
< f ,, g > (x , y) (z , w) = f x z , g y w

productSetoid : Setoid → Setoid → Setoid
productSetoid A B = record
  { Carrier = ⟨ A ⟩ × ⟨ B ⟩
  ; _≈_ = λ { (x , y) (w , z) → A ⟪ x ≈ w ⟫ × B ⟪ y ≈ z ⟫ }
  ; isEquivalence = record
    { refl = refl A , refl B
    ; sym = < sym A , sym B >
    ; trans = < trans A ,, trans B >
    }
  }

infixr 2 ⟪_×_⟫
⟪_×_⟫ = productSetoid
