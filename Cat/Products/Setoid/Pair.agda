open import Cat.Setoid renaming (module Setoid to S)

module Cat.Products.Setoid.Pair (A B : Setoid) where

open import Cat.Category
open import Cat.Product

open import Cat.Categories.Setoid
open import Cat.Setoids.Product

open Category setoidCategory

instance
  pairProduct : Product A B
  pairProduct = record
    { product = ⟪ A × B ⟫
    ; isProduct = record
      { fst = record { _$_ = fst ; cong-▸ = fst }
      ; snd = record { _$_ = snd ; cong-▸ = snd }
      ; factorProduct = λ f g → record
        { rightProductFactor = record { _$_ = λ x → (f $ x) , (g $ x) ; cong-▸ = λ p → cong-▸ f p , cong-▸ g p }
        ; rightProductFactorFstCommutes = λ _ → S.refl A
        ; rightProductFactorSndCommutes = λ _ → S.refl B
        ; rightProductFactorUnique = λ p q x → S.sym A (p x) , S.sym B (q x)
        }
      ; ≃-rightProductFactor-cong = λ p q x → p x , q x
      }
    }
