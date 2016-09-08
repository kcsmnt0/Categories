{-# OPTIONS --type-in-type #-}

module Cat.Category where

open import Cat.Setoid
open import Cat.Setoid public using (⟨_⟩)

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

record IsCategory {O} (_⇒_ : O → O → Setoid) : Set where
  infixr 8 _∘_
  field
    id : ∀ {a} → ⟨ a ⇒ a ⟩
    _∘_ : ∀ {a b c} → ⟨ b ⇒ c ⟩ → ⟨ a ⇒ b ⟩ → ⟨ a ⇒ c ⟩

    cong⟨_∘_⟩ : ∀
      {a b c}
      {f g : ⟨ a ⇒ b ⟩}
      {h i : ⟨ b ⇒ c ⟩}
      →
      (b ⇒ c) ⟪ h ≈ i ⟫ → (a ⇒ b) ⟪ f ≈ g ⟫ → (a ⇒ c) ⟪ h ∘ f ≈ i ∘ g ⟫

    idUnitᴸ : ∀ {a b} {f : ⟨ a ⇒ b ⟩} → (a ⇒ b) ⟪ id ∘ f ≈ f ⟫
    idUnitᴿ : ∀ {a b} {f : ⟨ a ⇒ b ⟩} → (a ⇒ b) ⟪ f ∘ id ≈ f ⟫

    assoc : ∀
      {a b c d}
      {g : ⟨ a ⇒ b ⟩}
      {h : ⟨ b ⇒ c ⟩}
      {i : ⟨ c ⇒ d ⟩}
      →
      (a ⇒ d) ⟪ i ∘ (h ∘ g) ≈ (i ∘ h) ∘ g ⟫
    
  -- there's probably some way to just re-export refl/sym/trans instead of redefining them?
  refl : ∀ {a b} {f : ⟨ a ⇒ b ⟩} → (a ⇒ b) ⟪ f ≈ f ⟫
  refl = Setoid.refl (_ ⇒ _)

  sym : ∀ {a b} {f g : ⟨ a ⇒ b ⟩} → (a ⇒ b) ⟪ f ≈ g ⟫ → (a ⇒ b) ⟪ g ≈ f ⟫
  sym = Setoid.sym (_ ⇒ _)

  trans : ∀ {a b} {f g h : ⟨ a ⇒ b ⟩} → (a ⇒ b) ⟪ f ≈ g ⟫ → (a ⇒ b) ⟪ g ≈ h ⟫ → (a ⇒ b) ⟪ f ≈ h ⟫
  trans = Setoid.trans (_ ⇒ _)

  infixr 1 _~_
  _~_ = trans

  cong⟨_∘⟩ : ∀ {a b c} {f : ⟨ a ⇒ b ⟩} {g h : ⟨ b ⇒ c ⟩} → (b ⇒ c) ⟪ g ≈ h ⟫ → (a ⇒ c) ⟪ g ∘ f ≈ h ∘ f ⟫
  cong⟨ p ∘⟩ = cong⟨ p ∘ refl ⟩

  cong⟨∘_⟩ : ∀ {a b c} {f g : ⟨ a ⇒ b ⟩} {h : ⟨ b ⇒ c ⟩} → (a ⇒ b) ⟪ f ≈ g ⟫ → (a ⇒ c) ⟪ h ∘ f ≈ h ∘ g ⟫
  cong⟨∘ p ⟩ = cong⟨ refl ∘ p ⟩

  homSetoid : ∀ {a b} → Setoid
  homSetoid {a} {b} = record
    { _≈_ = Setoid._≈_ (a ⇒ b)
    ; isEquivalence = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    }

  op : IsCategory (λ a b → b ⇒ a)
  op = record
    { id = id
    ; _∘_ = λ g f → f ∘ g
    ; idUnitᴸ = idUnitᴿ
    ; idUnitᴿ = idUnitᴸ
    ; assoc = sym assoc
    ; cong⟨_∘_⟩ = λ q p → cong⟨ p ∘ q ⟩
    }

  infix 4 _≃_
  _≃_ : ∀ {a b} → ⟨ a ⇒ b ⟩ → ⟨ a ⇒ b ⟩ → Set
  f ≃ g = (_ ⇒ _) ⟪ f ≈ g ⟫

  infix 1 begin_
  begin_ : ∀ {a b} {f g : ⟨ a ⇒ b ⟩} → (a ⇒ b) ⟪ f ≈ g ⟫ → (a ⇒ b) ⟪ f ≈ g ⟫
  begin p = p
  
  infix 3 _∎
  _∎ : ∀ {a b} (f : ⟨ a ⇒ b ⟩) → (a ⇒ b) ⟪ f ≈ f ⟫
  _ ∎ = refl
  
  infixr 2 _≃⟨_⟩_
  _≃⟨_⟩_ : ∀ {a b} (f : ⟨ a ⇒ b ⟩) {g h} → (a ⇒ b) ⟪ f ≈ g ⟫ → (a ⇒ b) ⟪ g ≈ h ⟫ → (a ⇒ b) ⟪ f ≈ h ⟫
  _ ≃⟨ p ⟩ q = trans p q

record Category : Set where
  infixr 0 _⇒_

  field
    Carrier : Set
    _⇒_ : Carrier → Carrier → Setoid
    isCategory : IsCategory _⇒_

  open IsCategory isCategory public renaming (op to isOp)

  op : Category
  op = record { isCategory = isOp }

open Category

[_] : Category → Set
[_] = Carrier
