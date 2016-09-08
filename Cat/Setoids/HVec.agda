module Cat.Setoids.HVec where

open import Cat.OPE
open import Cat.Setoid

open import Data.Fin
open import Data.Nat
open import Data.Vec

open Setoid

data HVec : ∀ {n} → Vec Setoid n → Set where
  [] : HVec []
  _∷_ : ∀ {A n} {As : Vec _ n} → ⟨ A ⟩ → HVec As → HVec (A ∷ As)

lookupH : ∀ {A n} {As : Vec _ n} → A ∈ As → HVec As → ⟨ A ⟩
lookupH here (x ∷ xs) = x
lookupH (there i) (x ∷ xs) = lookupH i xs

headH : ∀ {n} {As : Vec _ (suc n)} → HVec As → ⟨ head As ⟩
headH (x ∷ xs) = x

tailH : ∀ {n} {As : Vec _ (suc n)} → HVec As → HVec (tail As)
tailH (x ∷ xs) = xs

data _⟪_≊_⟫ : ∀ {n} (As : Vec _ n) → HVec As → HVec As → Set where
  [] : [] ⟪ [] ≊ [] ⟫
  _∷_ : ∀ {A n} {As : Vec _ n} {x y} {xs ys : HVec As} → A ⟪ x ≈ y ⟫ → As ⟪ xs ≊ ys ⟫ → (A ∷ As) ⟪ (x ∷ xs) ≊ (y ∷ ys) ⟫

_≊_ : ∀ {n} {As : Vec _ n} → HVec As → HVec As → Set
_≊_ = _ ⟪_≊_⟫

≊-lookupH-cong : ∀ {A n} {As : Vec _ n} {xs ys : HVec As} (i : A ∈ As) → xs ≊ ys → A ⟪ lookupH i xs ≈ lookupH i ys ⟫
≊-lookupH-cong here (p ∷ ps) = p
≊-lookupH-cong (there i) (p ∷ ps) = ≊-lookupH-cong i ps

≊-ope-subst-∈ : ∀ {A x m n} {xs : Vec A m} {ys : Vec A n} → OPE xs ys → x ∈ xs → x ∈ ys
≊-ope-subst-∈ (keep ope) here = here
≊-ope-subst-∈ (keep ope) (there i) = there (≊-ope-subst-∈ ope i)
≊-ope-subst-∈ (skip ope) i = there (≊-ope-subst-∈ ope i)

-- ≊-ope-subst-∈-lookupH-commutes : ∀ {A x m n} {xs : Vec A m} {ys : Vec A n} → OPE xs ys → x ∈ xs → x ∈ ys
-- ≊-ope-subst-∈-lookupH-commutes = {!!}

≊-refl : ∀ {n} {As : Vec _ n} {xs : HVec As} → xs ≊ xs
≊-refl {xs = []} = []
≊-refl {As = A ∷ As} {x ∷ xs} = refl A ∷ ≊-refl

≊-sym : ∀ {n} {As : Vec _ n} {xs ys : HVec As} → xs ≊ ys → ys ≊ xs
≊-sym [] = []
≊-sym {As = A ∷ As} (p ∷ ps) = sym A p ∷ ≊-sym ps

≊-trans : ∀ {n} {As : Vec _ n} {xs ys zs : HVec As} → xs ≊ ys → ys ≊ zs → xs ≊ zs
≊-trans [] [] = []
≊-trans {As = A ∷ As} (p ∷ ps) (q ∷ qs) = trans A p q ∷ ≊-trans ps qs

hvecSetoid : ∀ {n} → Vec Setoid n → Setoid
hvecSetoid As = record
  { Carrier = HVec As 
  ; _≈_ = _≊_
  ; isEquivalence = record { refl = ≊-refl ; sym = ≊-sym ; trans = ≊-trans }
  }

opeStripH : ∀ {m n} {As : Vec _ m} {Bs : Vec _ n} → OPE As Bs → HVec Bs → HVec As
opeStripH stop [] = []
opeStripH (keep p) (x ∷ xs) = x ∷ opeStripH p xs
opeStripH (skip p) (x ∷ xs) = opeStripH p xs
