{-# OPTIONS --type-in-type #-}

open import Cat.Category

open Category {{…}}

module Cat.Cones.FromQuiver
  {{C}} {A} (R : A → A → Set)
  {transport : A → [ C ]}
  (map : ∀ {a b} → R a b → ⟨ transport a ⇒ transport b ⟩)
  (apex : [ C ])
  (coneMap : ∀ {a} → ⟨ apex ⇒ transport a ⟩)
  (coneMapCommutes : ∀ {a b} (g : R a b) → map g ∘ coneMap ≃ coneMap)
  where

open import Cat.Cone
open import Cat.NaturalTransformation

open import Cat.Categories.Free R
open import Cat.Functors.Constant
open import Cat.Functors.FromQuiver R map

open import Cat.NaturalTransformations.FromQuiver
  R
  (λ _ → id)
  map
  coneMap
  (λ f → trans idUnitᴿ (sym (coneMapCommutes f)))

coneMapFromQuiverCommutes : ∀ {a b} (f : a ⟦⇒⟧ b) → coneMap ≃ quiverMap f ∘ coneMap
coneMapFromQuiverCommutes ⟦ f ⟧ = sym (coneMapCommutes f)
coneMapFromQuiverCommutes ⟦id⟧ = sym idUnitᴸ
coneMapFromQuiverCommutes (g ⟦∘⟧ f) =
  begin
    coneMap
  ≃⟨ coneMapFromQuiverCommutes g ⟩
    quiverMap g ∘ coneMap
  ≃⟨ cong⟨∘ coneMapFromQuiverCommutes f ⟩ ⟩
    quiverMap g ∘ (quiverMap f ∘ coneMap)
  ≃⟨ assoc ⟩
    (quiverMap g ∘ quiverMap f) ∘ coneMap
  ∎

naturalTransformation : NaturalTransformation (δ apex) functorFromQuiver
naturalTransformation = record
  { transform = transform naturalTransformationFromQuiver
  ; naturality = λ f → trans idUnitᴿ (coneMapFromQuiverCommutes f)
  }
  where
    open NaturalTransformation

open import Cat.Cones.FromNaturalTransformation apex functorFromQuiver naturalTransformation

instance
  coneFromQuiver : Cone functorFromQuiver
  coneFromQuiver = record
    { apex = apex
    ; isCone = record { coneMap = transform ; coneMapCommutes = λ f → sym (coneMapFromQuiverCommutes f) }
    }
    where
      open NaturalTransformation naturalTransformationFromQuiver
