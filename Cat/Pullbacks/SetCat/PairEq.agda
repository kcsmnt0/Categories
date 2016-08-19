{-# OPTIONS --type-in-type #-}

open import Cat.Setoid
open import Cat.Categories.Setoid renaming (_▸_ to _▹_)

module Cat.Pullbacks.SetCat.PairEq {{A B C : Setoid}} (f : ⟨ A ↦ B ⟩) (g : ⟨ C ↦ B ⟩) where

open import Cat.Category
open import Cat.Functor

open import Cat.Limits.Pullback as Pullback
open import Cat.Quivers.Pullback

open import Cat.Categories.Free _▸_

open import Data.Product as Product using (∃₂; _×_; _,_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open Setoid {{…}}

PairEq : Setoid
PairEq = record
  { Carrier = ∃₂ λ x y → B ⟪ (f $ x) ≈ (g $ y) ⟫
  ; _≈_ = λ { (x , y , _) (u , w , _) → A ⟪ x ≈ u ⟫ × C ⟪ y ≈ w ⟫ }
  ; isEquivalence = record
      { refl = refl , refl
      ; sym = Product.map sym sym
      ; trans = Product.zip trans trans
      }
  }

module PairEqFunctor where
  transport : V → Setoid
  transport α = A
  transport β = B
  transport γ = C
  
  pairEqMap : ∀ {i j : V} → i ▸ j → ⟨ transport i ↦ transport j ⟩
  pairEqMap φ = f
  pairEqMap ψ = g

  open import Cat.Functors.FromQuiver _▸_ pairEqMap public

open PairEqFunctor

open import Cat.Cone functorFromQuiver

module PairEqCone where
  coneMap : ∀ a → ⟨ PairEq ↦ transport a ⟩
  _$_ (coneMap α) (x , _ , _) = x
  _$_ (coneMap β) (x , _ , _) = f $ x
  _$_ (coneMap γ) (_ , y , _) = y
  cong-▸ (coneMap α) (p , _) = p
  cong-▸ (coneMap β) (p , _) = cong-▸ f p
  cong-▸ (coneMap γ) (_ , q) = q

  coneMapCommutes : ∀
    {a b}
    (f : a ▸ b)
    (x : ⟨ PairEq ⟩)
    →
    (transport b) ⟪ pairEqMap f $ coneMap a $ x ≈ coneMap b $ x ⟫
  coneMapCommutes φ _ = refl
  coneMapCommutes ψ (_ , _ , p) = sym p
  
  open import Cat.Cones.FromQuiver _▸_ pairEqMap PairEq (λ {a} → coneMap a) coneMapCommutes public

open PairEqCone using (coneFromQuiver)

instance
  pairEqPullback : Pullback functorFromQuiver
  pairEqPullback = record
    { cone = coneFromQuiver
    ; factor = λ c → let open Cone c in record
        { rightLimitFactor = record
            { _$_ = λ x →
                (coneMap {α} $ x) ,
                (coneMap {γ} $ x) ,
                trans (coneMapCommutes ⟦ φ ⟧ x) (sym (coneMapCommutes ⟦ ψ ⟧ x))
            ; cong-▸ = λ p → cong-▸ (coneMap {α}) p , cong-▸ (coneMap {γ}) p
            }
        ; rightLimitFactorCommutes = λ { {α} x → refl ; {β} x → sym (coneMapCommutes ⟦ φ ⟧ x) ; {γ} x → refl }
        ; rightLimitFactorUnique = λ g x → sym (g {α} x) , sym (g {γ} x)
        }
    ; ≃-rightLimitFactor-cong = λ p x → p {α} x , p {γ} x
    }
