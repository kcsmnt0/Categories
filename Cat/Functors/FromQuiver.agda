{-# OPTIONS --type-in-type #-}

open import Cat.Category

open Category {{…}}

-- a functor-ish mapping from a quiver to a category C gives rise to a functor from a free category to C
module Cat.Functors.FromQuiver
  {{C}} {A} (R : A → A → Set)
  {f : A → [ C ]}
  (g : ∀ {x y} → R x y → ⟨ f x ⇒ f y ⟩)
  where

open import Cat.Functor

open import Cat.Categories.Free R

quiverMap : ∀ {a b} → ⟨ a ⇒ b ⟩ → ⟨ f a ⇒ f b ⟩
quiverMap ⟦ h ⟧ = g h
quiverMap ⟦id⟧ = id
quiverMap (i ⟦∘⟧ h) = quiverMap i ∘ quiverMap h

≃-quiverMap-cong : {a b : A} {h i : ⟨ a ⇒ b ⟩} → h ≃ i → quiverMap h ≃ quiverMap i
≃-quiverMap-cong ⟦refl⟧ = refl
≃-quiverMap-cong (⟦sym⟧ p) = sym (≃-quiverMap-cong p)
≃-quiverMap-cong (⟦trans⟧ p q) = trans (≃-quiverMap-cong p) (≃-quiverMap-cong q)
≃-quiverMap-cong ⟦cong⟨ q ∘ p ⟩⟧ = cong⟨ ≃-quiverMap-cong q ∘ ≃-quiverMap-cong p ⟩
≃-quiverMap-cong ⟦idUnitᴸ⟧ = idUnitᴸ
≃-quiverMap-cong ⟦idUnitᴿ⟧ = idUnitᴿ
≃-quiverMap-cong ⟦assoc⟧ = assoc

instance
  functorFromQuiver : Functor freeCategory C
  functorFromQuiver = record
    { transport = f
    ; isFunctor = record
      { map = quiverMap
      ; ≃-map-id = refl
      ; ≃-map-∘ = refl
      ; ≃-map-cong = ≃-quiverMap-cong
      }
    }
