open import Cat.Category
open import Cat.Product

module Cat.Exponential {{C}} where

open import Cat.Functor

open import Cat.Endofunctors.Product C

open Category C
open Functor
open Product

record IsExponentialFactor
    {a b f f′}
    (_×a : ∀ x → Product x a)
    (eval : ⟨ product (f ×a) ⇒ b ⟩)
    (eval′ : ⟨ product (f′ ×a) ⇒ b ⟩)
    :
    Set where
  field
    rightExponentialFactor : ⟨ f′ ⇒ f ⟩

    rightExponentialFactorCommutes : eval ∘ map (fstFunctor _×a) rightExponentialFactor ≃ eval′
    rightExponentialFactorUnique : ∀ {g : ⟨ f′ ⇒ f ⟩} → eval ∘ map (fstFunctor _×a) g ≃ eval′ → g ≃ rightExponentialFactor

open IsExponentialFactor

record Exponential a b : Set where
  field
    pairFst : ∀ x → Product x a
    base : _
    eval : ⟨ product (pairFst base) ⇒ b ⟩
    factor : ∀ {f′} (eval′ : ⟨ product (pairFst f′) ⇒ b ⟩) → IsExponentialFactor pairFst eval eval′

    ≃-rightExponentialFactor-cong :
      {f g : ⟨ product (pairFst base) ⇒ b ⟩ }
      (_ : f ≃ g)
      →
      rightExponentialFactor (factor f) ≃ rightExponentialFactor (factor g)
