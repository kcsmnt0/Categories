open import Cat.Category

module Cat.Endofunctors.Product C where

open import Cat.Functor
open import Cat.Product {{C}}

open import Cat.Categories.Product C C renaming (productCategory to C×C)
open import Cat.Functors.Compose
open import Cat.Setoids.Product using (_,_)

open Product
open IsLeftProductFactor

open Category C

fstFunctor : ∀ {b} → (∀ a → Product a b) → Endofunctor C
fstFunctor {b} prod = record
  { transport = λ a → product (prod a)
  ; isFunctor = record
    { map = map
    ; ≃-map-id = sym (rightProductFactorUnique (mapFactor id) (trans idUnitᴸ (sym idUnitᴿ)) (sym idUnitᴿ))
    ; ≃-map-∘ = λ {x y z f g} →
       rightProductFactorUnique
         (mapFactor (g ∘ f))

         (begin
           (g ∘ f) ∘ fst (prod x)
         ≃⟨ sym assoc ⟩
           g ∘ (f ∘ fst (prod x))
         ≃⟨ cong⟨∘ rightProductFactorFstCommutes (mapFactor f) ⟩ ⟩
           g ∘ (fst (prod y) ∘ map f)
         ≃⟨ assoc ⟩
           (g ∘ fst (prod y)) ∘ map f
         ≃⟨ cong⟨ rightProductFactorFstCommutes (mapFactor g) ∘⟩ ⟩
           (fst (prod z) ∘ map g) ∘ map f
         ≃⟨ sym assoc ⟩
           fst (prod z) ∘ map g ∘ map f
         ∎)

         (begin
           snd (prod x)
         ≃⟨ rightProductFactorSndCommutes (mapFactor f) ⟩
           snd (prod y) ∘ map f
         ≃⟨ cong⟨ rightProductFactorSndCommutes (mapFactor g) ∘⟩ ⟩
           (snd (prod z) ∘ map g) ∘ map f
         ≃⟨ sym assoc ⟩
           snd (prod z) ∘ map g ∘ map f
         ∎)
    ; ≃-map-cong = λ {a c f g} p → ≃-rightProductFactor-cong (prod c) cong⟨ p ∘⟩ refl
    }
  }
  where
    mapFactor : ∀ {a c} (f : ⟨ a ⇒ c ⟩) → IsLeftProductFactor c b _ _ _ _
    mapFactor {a} {c} f = factorProduct (prod c) (f ∘ fst (prod a)) (snd (prod a))

    map : ∀ {a c} → ⟨ a ⇒ c ⟩ → ⟨ product (prod a) ⇒ product (prod c) ⟩
    map f = rightProductFactor (mapFactor f)

sndFunctor : ∀ {a} → (∀ b → Product a b) → Endofunctor C
sndFunctor {a} prod = record
  { transport = λ b → product (prod b)
  ; isFunctor = record
    { map = map
    ; ≃-map-id = sym (rightProductFactorUnique (mapFactor id) (sym idUnitᴿ) (trans idUnitᴸ (sym idUnitᴿ)))
    ; ≃-map-∘ = λ {x y z f g} →
       rightProductFactorUnique
         (mapFactor (g ∘ f))

         (begin
           fst (prod x)
         ≃⟨ rightProductFactorFstCommutes (mapFactor f) ⟩
           fst (prod y) ∘ map f
         ≃⟨ cong⟨ rightProductFactorFstCommutes (mapFactor g) ∘⟩ ⟩
           (fst (prod z) ∘ map g) ∘ map f
         ≃⟨ sym assoc ⟩
           fst (prod z) ∘ map g ∘ map f
         ∎)

         (begin
           (g ∘ f) ∘ snd (prod x)
         ≃⟨ sym assoc ⟩
           g ∘ (f ∘ snd (prod x))
         ≃⟨ cong⟨∘ rightProductFactorSndCommutes (mapFactor f) ⟩ ⟩
           g ∘ (snd (prod y) ∘ map f)
         ≃⟨ assoc ⟩
           (g ∘ snd (prod y)) ∘ map f
         ≃⟨ cong⟨ rightProductFactorSndCommutes (mapFactor g) ∘⟩ ⟩
           (snd (prod z) ∘ map g) ∘ map f
         ≃⟨ sym assoc ⟩
           snd (prod z) ∘ map g ∘ map f
         ∎)
    ; ≃-map-cong = λ {a c f g} p → ≃-rightProductFactor-cong (prod c) refl cong⟨ p ∘⟩
    }
  }
  where
    mapFactor : ∀ {b c} (f : ⟨ b ⇒ c ⟩) → IsLeftProductFactor a c _ _ _ _
    mapFactor {b} {c} f = factorProduct (prod c) (fst (prod b)) (f ∘ snd (prod b))

    map : ∀ {a c} → ⟨ a ⇒ c ⟩ → ⟨ product (prod a) ⇒ product (prod c) ⟩
    map f = rightProductFactor (mapFactor f)
