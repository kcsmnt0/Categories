module Cat.Functors.Semigroup where

open import Cat.Category
open import Cat.Functor using (Functor)
open import Cat.Setoid

open import Cat.Categories.Semigroup as Semigroup
open import Cat.Categories.Setoid as S
open import Cat.Structures.Semigroup
open import Cat.Setoids.FreeSemigroup as FS

open Setoid

map-⊕ : ∀ {A B} → (⟨ A ⟩ → ⟨ B ⟩) → FreeSemigroup A → FreeSemigroup B
map-⊕ f ⟦ x ⟧ = ⟦ f x ⟧
map-⊕ f (x ⟦⊕⟧ y) = map-⊕ f x ⟦⊕⟧ map-⊕ f y

cong-map-⊕ : ∀ {A B} (f : A S.▸ B) → ∀ {x y} → x ≊ y → map-⊕ {A} {B} (f $_) x ≊ map-⊕ (f $_) y
cong-map-⊕ f ⟦ p ⟧ = ⟦ cong-▸ f p ⟧
cong-map-⊕ f ≊-refl = ≊-refl
cong-map-⊕ f (≊-sym p) = ≊-sym (cong-map-⊕ f p)
cong-map-⊕ f (≊-trans p q) = ≊-trans (cong-map-⊕ f p) (cong-map-⊕ f q)
cong-map-⊕ f ≊-cong⟨ p ⊕ q ⟩ = ≊-cong⟨ cong-map-⊕ f p ⊕ cong-map-⊕ f q ⟩
cong-map-⊕ f ≊-assoc-⊕ = ≊-assoc-⊕

≊-map-id : ∀ {A} (x : FreeSemigroup A) → map-⊕ (λ y → y) x ≊ x
≊-map-id {A} ⟦ x ⟧ = ⟦ refl A ⟧
≊-map-id (x ⟦⊕⟧ y) = ≊-cong⟨ ≊-map-id x ⊕ ≊-map-id y ⟩

≊-map-∘ : ∀
  {A B C}
  (f : A S.▸ B)
  (g : B S.▸ C)
  (x : FreeSemigroup A)
  →
  map-⊕ {B} {C} (g $_) (map-⊕ (f $_) x) ≊ map-⊕ (λ y → g $ f $ y) x
≊-map-∘ f g ⟦ x ⟧ = ≊-refl
≊-map-∘ f g (x ⟦⊕⟧ y) = ≊-cong⟨ ≊-map-∘ f g x ⊕ ≊-map-∘ f g y ⟩

≊-map-cong : ∀
  {A B}
  (f g : A S.▸ B)
  (_ : ∀ x → B ⟪ f $ x ≈ g $ x ⟫)
  →
  ∀ x → map-⊕ {A} {B} (f $_) x ≊ map-⊕ (g $_) x
≊-map-cong f g p ⟦ x ⟧ = ⟦ p x ⟧
≊-map-cong f g p (x ⟦⊕⟧ y) = ≊-cong⟨ ≊-map-cong f g p x ⊕ ≊-map-cong f g p y ⟩

freeSemigroupFunctor : Functor setoidCategory semigroupCategory
freeSemigroupFunctor = record
  { transport = freeSemigroupSemigroup
  ; isFunctor = record
    { map = λ f → record
      { homomorphism = record { _$_ = map-⊕ (f $_) ; cong-▸ = cong-map-⊕ f }
      ; homomorphismPreservesAppend = ≊-refl
      }
    ; ≃-map-id = ≊-map-id
    ; ≃-map-∘ = λ {_ _ _ f g} → ≊-map-∘ f g
    ; ≃-map-cong = λ {_ _ f g} → ≊-map-cong f g
    }
  }

forgetSemigroupFunctor : Functor semigroupCategory setoidCategory
forgetSemigroupFunctor = record
  { transport = Semigroup.Carrier
  ; isFunctor = record
    { map = homomorphism
    ; ≃-map-id = λ {A} _ → refl (Semigroup.Carrier A)
    ; ≃-map-∘ = λ {A B C} _ → refl (Semigroup.Carrier C)
    ; ≃-map-cong = λ p x → p x
    }
  }
