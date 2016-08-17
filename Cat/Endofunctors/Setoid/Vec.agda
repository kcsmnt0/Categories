{-# OPTIONS --type-in-type #-}

module Cat.Endofunctors.Setoid.Vec where

open import Cat.Category
open import Cat.Functor using (_∙_; Endofunctor)
open import Cat.Isomorphism
open import Cat.NaturalTransformation
open import Cat.Representable
open import Cat.Setoid renaming (module Setoid to S)

open import Cat.Categories.Setoid
open import Cat.Functors.Hom
open import Cat.Setoids.SetSetoid
import Cat.NaturalIsomorphisms.Yoneda as Yoneda

open import Data.Fin hiding (strengthen)
open import Data.Nat
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as PE

open Category setoidCategory
open NaturalTransformation

FinS : ℕ → Setoid
FinS n = setSetoid (Fin n)

sucS : ∀ {n} → FinS n ▸ FinS (suc n)
sucS = record { _$_ = suc ; cong-▸ = cong suc }

data Vec (A : Setoid) : ℕ → Set where
  [] : Vec A 0
  _∷_ : ∀ {n} → ⟨ A ⟩ → Vec A n → Vec A (suc n)

infix 1 _≊_
data _≊_ {A : Setoid} : ∀ {n} → Vec A n → Vec A n → Set where
  [] : [] ≊ []
  _∷_ : ∀ {a b n} {as bs : Vec A n} → A ⟪ a ≈ b ⟫ → as ≊ bs → a ∷ as ≊ b ∷ bs

≊-refl : ∀ {A n} {as : Vec A n} → as ≊ as
≊-refl {as = []} = []
≊-refl {A} {as = _ ∷ as} = S.refl A ∷ ≊-refl

≊-sym : ∀ {A n} {as bs : Vec A n} → as ≊ bs → bs ≊ as
≊-sym [] = []
≊-sym {A} (p ∷ ps) = S.sym A p ∷ ≊-sym ps

≊-trans : ∀ {A n} {as bs cs : Vec A n} → as ≊ bs → bs ≊ cs → as ≊ cs
≊-trans [] [] = []
≊-trans {A} (p ∷ ps) (q ∷ qs) = S.trans A p q ∷ ≊-trans ps qs

VecS : ∀ A n → Setoid
VecS A n = record
  { _≈_ = _≊_ {A} {n}
  ; isEquivalence = record
      { refl = ≊-refl
      ; sym = ≊-sym
      ; trans = ≊-trans
      }
  }

map : ∀ {A B n} → A ▸ B → Vec A n → Vec B n
map f [] = []
map f (a ∷ as) = (f $ a) ∷ map f as

cong-map-▸ : ∀ {A B n} {f : A ▸ B} {xs ys : Vec A n} → xs ≊ ys → map f xs ≊ map f ys
cong-map-▸ [] = []
cong-map-▸ {f = f} (p ∷ ps) = cong-▸ f p ∷ cong-map-▸ ps

mapS : ∀ {A B n} → A ▸ B → ⟨ VecS A n ↦ VecS B n ⟩
mapS f = record { _$_ = map f ; cong-▸ = cong-map-▸ }

≊-map-id : ∀ {A n} (xs : Vec A n) → map id xs ≊ xs
≊-map-id [] = []
≊-map-id {A} (x ∷ xs) = S.refl A ∷ ≊-map-id xs

≊-map-∘ : ∀ {A B C n} {f : A ▸ B} {g : B ▸ C} (xs : Vec A n) → map g (map f xs) ≊ map (g ∘ f) xs
≊-map-∘ [] = []
≊-map-∘ {C = C} (x ∷ xs) = S.refl C ∷ ≊-map-∘ xs

≊-map-cong : ∀ {A B n} {f g : A ▸ B} → (∀ xs → B ⟪ f $ xs ≈ g $ xs ⟫) → (xs : Vec A n) → map f xs ≊ map g xs
≊-map-cong p [] = []
≊-map-cong p (x ∷ xs) = p x ∷ ≊-map-cong p xs

instance
  vecFunctor : ∀ {n} → Endofunctor setoidCategory
  vecFunctor {n} = record
    { isFunctor = record
      { map = mapS {n = n} 
      ; ≃-map-id = ≊-map-id
      ; ≃-map-∘ = ≊-map-∘
      ; ≃-map-cong = ≊-map-cong
      }
    }

index : ∀ {A n} → Vec A n → Fin n → ⟨ A ⟩
index (x ∷ xs) zero = x
index (x ∷ xs) (suc n) = index xs n

cong-index-▸ : ∀ {A n} {xs ys : Vec A n} → xs ≊ ys → ∀ i → A ⟪ index xs i ≈ index ys i ⟫
cong-index-▸ (p ∷ ps) zero = p
cong-index-▸ (p ∷ ps) (suc i) = cong-index-▸ ps i

indexS : ∀ {A n} → ⟨ VecS A n ↦ FinS n ↦ A ⟩
indexS {A} = record
  { _$_ = λ xs → record { _$_ = index xs ; cong-▸ = λ { {_}.{_} refl → S.refl A } }
  ; cong-▸ = cong-index-▸
  }

indexNaturality : ∀ {A B n} (g : A ▸ B) (xs : Vec A n) (i : Fin n) → B ⟪ index (map g xs) i ≈ (g $ index xs i) ⟫
indexNaturality {A} g (x ∷ xs) zero = cong-▸ g (S.refl A)
indexNaturality g (x ∷ xs) (suc i) = indexNaturality g xs i

indexNT : ∀ {n} → NaturalTransformation (vecFunctor {n}) (homFunctor (FinS n))
indexNT = record { transform = indexS ; naturality = indexNaturality }

fins : ∀ {n} → Vec (FinS n) n
fins {zero} = []
fins {suc n} = zero ∷ map (record { _$_ = suc ; cong-▸ = cong suc }) fins

memoNT : ∀ {n} → NaturalTransformation (homFunctor (FinS n)) (vecFunctor {n})
memoNT {n} = let open Yoneda (vecFunctor {n}) in transform yonedaToNaturalTransformation $ fins

memoS : ∀ {A n} → ⟨ (FinS n ↦ A) ↦ VecS A n ⟩
memoS = transform memoNT

memo : ∀ {A n} → (Fin n → ⟨ A ⟩) → Vec A n
memo {A} f = memoS $ record { _$_ = f ; cong-▸ = λ { {_}.{_} refl → S.refl A } }

mapIndexFinsCancel : ∀ {A n} → transform memoNT ∘ transform (indexNT {n}) {A} ≃ id
mapIndexFinsCancel [] = []
mapIndexFinsCancel {A} (x ∷ xs) =
  S.refl A ∷
    ≊-trans
      (≊-map-∘ fins)
      (≊-trans
        (≊-map-cong (λ _ → S.refl A) fins)
        (mapIndexFinsCancel xs))

indexMapFinsCancel : ∀ {A n} → transform (indexNT {n}) {A} ∘ transform memoNT ≃ id
indexMapFinsCancel {A} f zero = S.refl A
indexMapFinsCancel {A} f (suc i) =
  S.trans A
    (indexNaturality f fins (suc i))
    (cong-▸ f (indexMapFinsCancel sucS i))

vecFunctorRepresentable : ∀ {n} → IsRepresentable (vecFunctor {n}) (FinS n)
vecFunctorRepresentable {n} = naturalIsomorphismFromNaturalTransformations memoNT indexNT record
  { cancelLR = mapIndexFinsCancel
  ; cancelRL = indexMapFinsCancel
  }
  where
    open import Cat.NaturalIsomorphisms.FromNaturalTransformations (homFunctor (FinS n)) vecFunctor
