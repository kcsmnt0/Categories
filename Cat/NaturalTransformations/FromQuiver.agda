{-# OPTIONS --type-in-type #-}

open import Cat.Category

open Category {{…}}

module Cat.NaturalTransformations.FromQuiver
  {{C}} {A} (R : A → A → Set)
  {f g : A → [ C ]}
  (h : ∀ {a b} → R a b → ⟨ f a ⇒ f b ⟩)
  (i : ∀ {a b} → R a b → ⟨ g a ⇒ g b ⟩)
  (α : ∀ {a} → ⟨ f a ⇒ g a ⟩)
  (naturality : ∀ {a b} (j : R a b) → α ∘ h j ≃ i j ∘ α)
  where

open import Cat.Functor
open import Cat.NaturalTransformation

open import Cat.Categories.Free R
open import Cat.Functors.FromQuiver R h renaming (quiverMap to mapʰ; functorFromQuiver to functorʰ)
open import Cat.Functors.FromQuiver R i renaming (quiverMap to mapⁱ; functorFromQuiver to functorⁱ)

⟦naturality⟧ : ∀ {a b} (f : a ⟦⇒⟧ b) → α ∘ mapʰ f ≃ mapⁱ f ∘ α
⟦naturality⟧ ⟦ j ⟧ = naturality j
⟦naturality⟧ ⟦id⟧ = trans idUnitᴿ (sym idUnitᴸ)
⟦naturality⟧ (k ⟦∘⟧ j) =
  begin
    α ∘ (mapʰ k ∘ mapʰ j)
  ≃⟨ assoc ⟩
    (α ∘ mapʰ k) ∘ mapʰ j
  ≃⟨ cong⟨ ⟦naturality⟧ k ∘⟩ ⟩
    (mapⁱ k ∘ α) ∘ mapʰ j
  ≃⟨ sym assoc ⟩
    mapⁱ k ∘ (α ∘ mapʰ j)
  ≃⟨ cong⟨∘ ⟦naturality⟧ j ⟩ ⟩
    mapⁱ k ∘ (mapⁱ j ∘ α)
  ≃⟨ assoc ⟩
    (mapⁱ k ∘ mapⁱ j) ∘ α
  ∎

instance
  naturalTransformationFromQuiver : NaturalTransformation functorʰ functorⁱ
  naturalTransformationFromQuiver = record
    { transform = α
    ; naturality = ⟦naturality⟧
    }
