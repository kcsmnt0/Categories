open import Cat.Setoid renaming (module Setoid to S)

module Cat.Exponentials.Setoid.Function (A B : Setoid) where

open import Cat.Category
open import Cat.Exponential

open import Cat.Categories.Setoid
open import Cat.Products.Setoid.Pair
open import Cat.Setoids.Product

open Category setoidCategory

instance
  functionExponential : Exponential A B
  functionExponential = record
    { pairFst = λ _ → pairProduct _ _
    ; base = A ↦ B
    ; eval = record
      { _$_ = λ { (f , x) → f $ x }
      ; cong-▸ = λ { {f , x} {g , y} (p , q) → S.trans B (cong-▸ f q) (p y) }
      }
    ; factor = λ {f′} eval′ → record
      { rightExponentialFactor = record
        { _$_ = λ f → record
          { _$_ = λ a → eval′ $ (f , a)
          ; cong-▸ = λ p → cong-▸ eval′ (S.refl f′ , p)
          }
        ; cong-▸ = λ p _ → cong-▸ eval′ (p , S.refl A)
        }
      ; rightExponentialFactorCommutes = λ _ → cong-▸ eval′ (S.refl f′ , S.refl A)
      ; rightExponentialFactorUnique = λ p _ _ → p _
      }
    ; ≃-rightExponentialFactor-cong = λ p _ _ → p _
    }
