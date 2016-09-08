{-# OPTIONS --type-in-type #-}

module Cat.OPE where

open import Data.Fin
open import Data.Vec

open import Relation.Binary.PropositionalEquality

-- an order-preserving embedding between Vecs, or a witness to an injection
data OPE {A} : ∀ {m n} → Vec A m → Vec A n → Set where
  stop : OPE [] []
  keep : ∀ {m n x} {xs : Vec A m} {ys : Vec A n} → OPE xs ys → OPE (x ∷ xs) (x ∷ ys)
  skip : ∀ {m n x} {xs : Vec A m} {ys : Vec A n} → OPE xs ys → OPE xs (x ∷ ys)

opeId : ∀ {A n} {xs : Vec A n} → OPE xs xs
opeId {xs = []} = stop
opeId {xs = x ∷ xs} = keep opeId

opeWeaken : ∀ {A n x} {xs : Vec A n} → OPE xs (x ∷ xs)
opeWeaken = skip opeId

opeFin : ∀ {A m n} {xs : Vec A m} {ys : Vec A n} → OPE xs ys → Fin m → Fin n
opeFin (keep p) zero = zero
opeFin (skip p) zero = suc (opeFin p zero)
opeFin (keep p) (suc i) = suc (opeFin p i)
opeFin (skip p) (suc i) = suc (opeFin p (suc i))

opeFinLookupCommutes : ∀ {A m n} {xs : Vec A m} {ys : Vec A n} (p : OPE xs ys) i → lookup i xs ≡ lookup (opeFin p i) ys
opeFinLookupCommutes (keep p) zero = refl
opeFinLookupCommutes (skip p) zero = opeFinLookupCommutes p zero
opeFinLookupCommutes (keep p) (suc i) = opeFinLookupCommutes p i
opeFinLookupCommutes (skip p) (suc i) = opeFinLookupCommutes p (suc i)
