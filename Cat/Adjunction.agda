open import Cat.Category
open import Cat.Functor

module Cat.Adjunction where

open import Cat.Bifunctor
open import Cat.NaturalIsomorphism

open import Cat.Categories.Category
open import Cat.Categories.Setoid
open import Cat.Endofunctors.Identity
open import Cat.Functors.Compose
open import Cat.Functors.Hom
open import Cat.Setoids.Product

open Functor
open Isomorphism
open NaturalTransformation

record Adjunction {{C D}} (L : Functor C D) (R : Functor D C) : Set where
  -- auto instance resolution (open Category {{…}}) gets reeeeally slow in this file for some reason
  open Category C renaming
    ( _⇒_ to _⇒ᶜ_
    ; _≃_ to _≃ᶜ_
    ; id to idᶜ
    ; _∘_ to _∘ᶜ_
    ; idUnitᴸ to idUnitᴸᶜ
    ; idUnitᴿ to idUnitᴿᶜ
    ; assoc to assocᶜ
    ; begin_ to beginᶜ_
    ; _≃⟨_⟩_ to _≃ᶜ⟨_⟩_
    ; _∎ to _∎ᶜ
    ; cong⟨_∘_⟩ to cong⟨_∘ᶜ_⟩
    ; cong⟨_∘⟩ to cong⟨_∘ᶜ⟩
    ; cong⟨∘_⟩ to cong⟨∘ᶜ_⟩
    ; refl to reflᶜ
    ; sym to symᶜ
    ; trans to transᶜ
    ; _~_ to _~ᶜ_
    )

  open Category D renaming
    ( _⇒_ to _⇒ᵈ_
    ; _≃_ to _≃ᵈ_
    ; id to idᵈ
    ; _∘_ to _∘ᵈ_
    ; idUnitᴸ to idUnitᴸᵈ
    ; idUnitᴿ to idUnitᴿᵈ
    ; assoc to assocᵈ
    ; begin_ to beginᵈ_
    ; _≃⟨_⟩_ to _≃ᵈ⟨_⟩_
    ; _∎ to _∎ᵈ
    ; cong⟨_∘_⟩ to cong⟨_∘ᵈ_⟩
    ; cong⟨_∘⟩ to cong⟨_∘ᵈ⟩
    ; cong⟨∘_⟩ to cong⟨∘ᵈ_⟩
    ; refl to reflᵈ
    ; sym to symᵈ
    ; trans to transᵈ
    ; _~_ to _~ᵈ_
    )

  field
    unit : NaturalTransformation identityFunctor (R ⊚ L)
    counit : NaturalTransformation (L ⊚ R) identityFunctor

    consistencyᴸ : ∀ {a} → idᵈ ≃ᵈ transform counit ∘ᵈ map L (transform unit {a}) -- L ⇒ L∘R∘L ⇒ L
    consistencyᴿ : ∀ {a} → idᶜ ≃ᶜ map R (transform counit {a}) ∘ᶜ transform unit -- R ⇒ R∘L∘R ⇒ R

  rightAdjunct : ∀ {a b} → (L ∙ a ⇒ᵈ b) ▸ (a ⇒ᶜ R ∙ b)
  rightAdjunct = record
    { _$_ = λ f → map R f ∘ᶜ transform unit
    ; cong-▸ = λ p → cong⟨ ≃-map-cong R p ∘ᶜ⟩
    }

  leftAdjunct : ∀ {a b} → (a ⇒ᶜ R ∙ b) ▸ (L ∙ a ⇒ᵈ b)
  leftAdjunct = record
    { _$_ = λ f → transform counit ∘ᵈ map L f
    ; cong-▸ = λ p → cong⟨∘ᵈ ≃-map-cong L p ⟩
    }

  leftHomProfunctor : Profunctor _ _
  leftHomProfunctor = homProfunctorUnderFunctors L identityFunctor

  rightHomProfunctor : Profunctor _ _
  rightHomProfunctor = homProfunctorUnderFunctors identityFunctor R

  naturalityᴿ : Naturality leftHomProfunctor rightHomProfunctor rightAdjunct
  naturalityᴿ (f , g) h =
    beginᶜ
      map R (g ∘ᵈ (h ∘ᵈ map L f)) ∘ᶜ transform unit
    ≃ᶜ⟨ cong⟨ symᶜ (≃-map-∘ R) ~ᶜ cong⟨∘ᶜ symᶜ (≃-map-∘ R) ⟩ ∘ᶜ⟩ ⟩
      (map R g ∘ᶜ (map R h ∘ᶜ map (R ⊚ L) f)) ∘ᶜ transform unit
    ≃ᶜ⟨ symᶜ assocᶜ ~ᶜ cong⟨∘ᶜ symᶜ assocᶜ ⟩ ⟩
      map R g ∘ᶜ (map R h ∘ᶜ (map (R ⊚ L) f ∘ᶜ transform unit))
    ≃ᶜ⟨ cong⟨∘ᶜ cong⟨∘ᶜ symᶜ (naturality unit _) ⟩ ⟩ ⟩
      map R g ∘ᶜ (map R h ∘ᶜ (transform unit ∘ᶜ f))
    ≃ᶜ⟨ cong⟨∘ᶜ assocᶜ ⟩ ⟩
      (map R g ∘ᶜ ((map R h ∘ᶜ transform unit) ∘ᶜ f))
    ∎ᶜ

  naturalityᴸ : Naturality rightHomProfunctor leftHomProfunctor leftAdjunct
  naturalityᴸ (f , g) h =
    beginᵈ
      transform counit ∘ᵈ map L (map R g ∘ᶜ (h ∘ᶜ f))
    ≃ᵈ⟨ cong⟨∘ᵈ symᵈ (≃-map-∘ L) ~ᵈ cong⟨∘ᵈ symᵈ (≃-map-∘ L) ⟩ ⟩ ⟩
      transform counit ∘ᵈ (map (L ⊚ R) g ∘ᵈ (map L h ∘ᵈ map L f))
    ≃ᵈ⟨ assocᵈ ⟩
      (transform counit ∘ᵈ map (L ⊚ R) g) ∘ᵈ (map L h ∘ᵈ map L f)
    ≃ᵈ⟨ cong⟨ naturality counit _ ∘ᵈ⟩ ⟩
      (g ∘ᵈ transform counit) ∘ᵈ (map L h ∘ᵈ map L f)
    ≃ᵈ⟨ symᵈ assocᵈ ~ᵈ cong⟨∘ᵈ assocᵈ ⟩ ⟩
      (g ∘ᵈ ((transform counit ∘ᵈ map L h) ∘ᵈ map L f))
    ∎ᵈ

  adjunctionIsomorphism : ∀ {a b} → (L ∙ a ⇒ᵈ b) ⇔ (a ⇒ᶜ R ∙ b)
  adjunctionIsomorphism = record
      { right = rightAdjunct
      ; left = leftAdjunct
      ; isIsomorphism = record
        { cancelLR = λ f →
            beginᶜ
              map R (transform counit ∘ᵈ map L f) ∘ᶜ transform unit
            ≃ᶜ⟨ cong⟨ ≃-map-cong R cong⟨∘ᵈ symᵈ idUnitᴸᵈ ⟩ ∘ᶜ⟩ ⟩
              map R (transform counit ∘ᵈ (idᵈ ∘ᵈ map L f)) ∘ᶜ transform unit
            ≃ᶜ⟨ naturalityᴿ _ _ ⟩
              (map R (transform counit) ∘ᶜ ((map R idᵈ ∘ᶜ transform unit) ∘ᶜ f))
            ≃ᶜ⟨ cong⟨∘ᶜ cong⟨ cong⟨ ≃-map-id R ∘ᶜ⟩ ~ᶜ idUnitᴸᶜ ∘ᶜ⟩ ⟩ ~ᶜ assocᶜ ⟩
              (map R (transform counit) ∘ᶜ transform unit) ∘ᶜ f
            ≃ᶜ⟨ cong⟨ symᶜ consistencyᴿ ∘ᶜ⟩ ⟩
              idᶜ ∘ᶜ f
            ≃ᶜ⟨ idUnitᴸᶜ ⟩
              f
            ∎ᶜ
        ; cancelRL = λ f →
            beginᵈ
              transform counit ∘ᵈ map L (map R f ∘ᶜ transform unit)
            ≃ᵈ⟨ cong⟨∘ᵈ ≃-map-cong L cong⟨∘ᶜ symᶜ idUnitᴸᶜ ⟩ ⟩ ⟩
              transform counit ∘ᵈ map L (map R f ∘ᶜ (idᶜ ∘ᶜ transform unit))
            ≃ᵈ⟨ naturalityᴸ _ _ ⟩
              f ∘ᵈ ((transform counit ∘ᵈ map L idᶜ) ∘ᵈ map L (transform unit))
            ≃ᵈ⟨ cong⟨∘ᵈ cong⟨ cong⟨∘ᵈ ≃-map-id L ⟩ ~ᵈ idUnitᴿᵈ ∘ᵈ⟩ ⟩ ⟩
              f ∘ᵈ (transform counit ∘ᵈ map L (transform unit))
            ≃ᵈ⟨ cong⟨∘ᵈ symᵈ consistencyᴸ ⟩ ⟩
              f ∘ᵈ idᵈ
            ≃ᵈ⟨ idUnitᴿᵈ ⟩
              f
            ∎ᵈ
        }
      }

  adjunctionNaturalIsomorphism : NaturalIsomorphism leftHomProfunctor rightHomProfunctor
  adjunctionNaturalIsomorphism = record
    { transformIso = adjunctionIsomorphism
    ; naturalityᴿ = naturalityᴿ
    ; naturalityᴸ = naturalityᴸ
    }

infix 4 _⊣_
_⊣_ = Adjunction

record LeftAdjoint {{C D}} (R : Functor D C) : Set where
  field
    leftAdjoint : Functor C D
    adjunction : Adjunction leftAdjoint R

  open Adjunction adjunction public

record RightAdjoint {{C D}} (L : Functor C D) : Set where
  field
    rightAdjoint : Functor D C
    adjunction : Adjunction L rightAdjoint

  open Adjunction adjunction public
