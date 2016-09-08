{-# OPTIONS --type-in-type #-}

module Cat.Functor where

open import Cat.Category
open import Cat.Setoid

open import Cat.Categories.Setoid using (setoidCategory)

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Category {{…}}

record IsFunctor {{C D}} (f : [ C ] → [ D ]) : Set where
  field
    map : ∀ {a b} → ⟨ a ⇒ b ⟩ → ⟨ f a ⇒ f b ⟩

    ≃-map-id : ∀ {a} → map {a} id ≃ id {a = f a}
    ≃-map-∘ : ∀ {a b c} {f : ⟨ a ⇒ b ⟩} {g : ⟨ b ⇒ c ⟩} → map g ∘ map f ≃ map (g ∘ f)
    ≃-map-cong : ∀ {a b} {f g : ⟨ a ⇒ b ⟩} → f ≃ g → map f ≃ map g

record Functor (C D : Category) : Set where
  field
    transport : [ C ] → [ D ]
    instance isFunctor : IsFunctor {{C}} {{D}} transport

  open IsFunctor isFunctor public

open Functor

infixr 1 _∙_
_∙_ : ∀ {{C D}} → Functor C D → [ C ] → [ D ]
_∙_ = transport

Endofunctor : Category → Set
Endofunctor C = Functor C C

Contrafunctor : Category → Category → Set
Contrafunctor C D = Functor (Category.op C) D

data _≊_ {{C D}} : Functor C D → Functor C D → Set where
  ⟦_⟧ :
    {α : [ C ] → [ D ]}
    {F G : IsFunctor α}
    →
    (∀ {a b} {f : ⟨ a ⇒ b ⟩} → IsFunctor.map F f ≃ IsFunctor.map G f)
    →
    record { isFunctor = F } ≊ record { isFunctor = G }

≊-refl : ∀ {{C D}} {F : Functor C D} → F ≊ F
≊-refl = ⟦ refl ⟧

≊-sym : ∀ {{C D}} {F G : Functor C D} → F ≊ G → G ≊ F
≊-sym ⟦ p ⟧ = ⟦ sym p ⟧

≊-trans : ∀ {{C D}} {F G H : Functor C D} → F ≊ G → G ≊ H → F ≊ H
≊-trans ⟦ p ⟧ ⟦ q ⟧ = ⟦ trans p q ⟧

instance
  functorSetoid : ∀ {{C D}} → Setoid
  functorSetoid {{C}} {{D}} = record
    { Carrier = Functor C D
    ; _≈_ = _≊_
    ; isEquivalence = record
      { refl = ≊-refl
      ; sym = ≊-sym
      ; trans = ≊-trans
      }
    }
