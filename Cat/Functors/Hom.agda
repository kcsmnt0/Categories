{-# OPTIONS --type-in-type #-}

open import Cat.Category

module Cat.Functors.Hom {{C}} (a : [ C ]) where

open import Cat.Functor
open import Cat.Setoid

open import Cat.Categories.Setoid

open Category C

instance
  homFunctor : Functor C setoidCategory
  homFunctor = record
    { transport = λ b → a ⇒ b
    ; isFunctor = record
      { map = λ {b}{c} g → record
        { _$_ = g ∘_
        ; cong-▸ = cong⟨ refl ∘_⟩
        }
      ; ≃-map-id = λ _ → idUnitᴸ
      ; ≃-map-∘ = λ _ → assoc
      ; ≃-map-cong = λ p _ → cong⟨ p ∘ refl ⟩
      }
    }

  homContrafunctor : Contrafunctor C setoidCategory
  homContrafunctor = record
    { transport = λ b → b ⇒ a
    ; isFunctor = record
      { map = λ {b}{c} g → record
        { _$_ = _∘ g
        ; cong-▸ = cong⟨_∘ refl ⟩
        }
      ; ≃-map-id = λ _ → idUnitᴿ
      ; ≃-map-∘ = λ _ → sym assoc
      ; ≃-map-cong = λ p _ → cong⟨ refl ∘ p ⟩
      }
    }
