open import Cat.Category
open import Cat.Functor

module Cat.Adjunction {{C D : Category}} where

open import Cat.Bifunctor
open import Cat.NaturalIsomorphism

open import Cat.Categories.Category
open import Cat.Categories.Setoid
open import Cat.Functors.Hom
open import Cat.Setoids.Product

open Category {{…}}
open Functor
open Isomorphism
open NaturalTransformation

Adjunction : Functor C D → Functor D C → Set
Adjunction L R = NaturalIsomorphism (homProfunctorUnderFunctors L id) (homProfunctorUnderFunctors id R)

_⊣_ = Adjunction

module AdjunctionIsomorphism {L R} (adj : L ⊣ R) where
  open NaturalIsomorphism adj
  
  rightAdjunct : ∀ {a b} → (L ∙ a ⇒ b) ▸ (a ⇒ R ∙ b)
  rightAdjunct = right transformIso

  leftAdjunct : ∀ {a b} → (a ⇒ R ∙ b) ▸ (L ∙ a ⇒ b)
  leftAdjunct = left transformIso

  -- naturalityᴿ : rightAdjunct (g ∘ h ∘ L f) ≃ R g ∘ rightAdjunct h ∘ f
  -- naturalityᴸ : leftAdjunct (R g ∘ h ∘ f) ≃ g ∘ leftAdjunct h ∘ L f

  unit : NaturalTransformation id (R ∘ L)
  unit = record
    { transform = rightAdjunct $ id
    ; naturality = λ f →
        begin
          (rightAdjunct $ id) ∘ f
        ≃⟨ sym idUnitᴸ ~ cong⟨ sym (≃-map-id R) ∘⟩ ⟩
          map R id ∘ ((rightAdjunct $ id) ∘ f)
        ≃⟨ sym (naturalityᴿ (f , id) id) ⟩
          (rightAdjunct $ (id ∘ (id ∘ map L f)))
        ≃⟨ cong-▸ rightAdjunct (idUnitᴸ ~ idUnitᴸ ~ sym idUnitᴿ ~ cong⟨∘ sym idUnitᴿ ~ cong⟨∘ sym (≃-map-id L) ⟩ ⟩) ⟩
          (rightAdjunct $ (map L f ∘ (id ∘ map L id)))
        ≃⟨ naturalityᴿ (id , map L f) id ⟩
          map (R ∘ L) f ∘ ((rightAdjunct $ id) ∘ id)
        ≃⟨ cong⟨∘ idUnitᴿ ⟩ ⟩
          map (R ∘ L) f ∘ (rightAdjunct $ id)
        ∎
    }

  counit : NaturalTransformation (L ∘ R) id
  counit = record
    { transform = leftAdjunct $ id
    ; naturality = λ f →
        begin
          (leftAdjunct $ id) ∘ map (L ∘ R) f
        ≃⟨ sym idUnitᴸ ⟩
          id ∘ ((leftAdjunct $ id) ∘ map L (map R f))
        ≃⟨ sym (naturalityᴸ _ _) ⟩
          (leftAdjunct $ (map R id ∘ (id ∘ map R f)))
        ≃⟨ cong-▸ leftAdjunct (cong⟨ ≃-map-id R ∘⟩ ~ idUnitᴸ ~ idUnitᴸ ~ sym idUnitᴿ ~ cong⟨∘ sym idUnitᴿ ~ cong⟨∘ sym (≃-map-id R) ⟩ ⟩ ) ⟩
          (leftAdjunct $ (map R f ∘ (id ∘ map R id)))
        ≃⟨ naturalityᴸ _ _ ⟩
          f ∘ ((leftAdjunct $ id) ∘ map (L ∘ R) id)
        ≃⟨ cong⟨∘ cong⟨∘ ≃-map-id (L ∘ R) ⟩ ~ idUnitᴿ ⟩ ⟩
          f ∘ (leftAdjunct $ id)
        ∎
    }

  -- R ⇒ R∘L∘R ⇒ R
  consistencyᴿ : ∀ {a} → id ≃ transform counit ∘ map L (transform unit {a})
  consistencyᴿ =
    begin
      id
    ≃⟨ sym (cancelRL transformIso id) ⟩
      (leftAdjunct $ (rightAdjunct $ id))
    ≃⟨ cong-▸ leftAdjunct (sym idUnitᴸ ~ cong⟨ sym (≃-map-id R) ∘ sym idUnitᴸ ⟩) ⟩
      (leftAdjunct $ (map R id ∘ (id ∘ (rightAdjunct $ id))))
    ≃⟨ naturalityᴸ _ _ ⟩
      id ∘ ((leftAdjunct $ id) ∘ map L (rightAdjunct $ id))
    ≃⟨ idUnitᴸ ⟩
      (leftAdjunct $ id) ∘ map L (rightAdjunct $ id)
    ∎

  -- L ⇒ L∘R∘L ⇒ L
  consistencyᴸ : ∀ {a} → id ≃ map R (transform counit {a}) ∘ transform unit
  consistencyᴸ =
    begin
      id
    ≃⟨ sym (cancelLR transformIso _) ⟩
      (rightAdjunct $ (leftAdjunct $ id))
    ≃⟨ cong-▸ rightAdjunct (sym idUnitᴿ ~ cong⟨∘ sym idUnitᴿ ~ cong⟨∘ sym (≃-map-id L) ⟩ ⟩) ⟩
      (rightAdjunct $ ((leftAdjunct $ id) ∘ (id ∘ map L id)))
    ≃⟨ naturalityᴿ _ _ ⟩
      map R (leftAdjunct $ id) ∘ ((rightAdjunct $ id) ∘ id)
    ≃⟨ cong⟨∘ idUnitᴿ ⟩ ⟩
      map R (leftAdjunct $ id) ∘ (rightAdjunct $ id)
    ∎
