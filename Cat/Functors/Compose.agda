open import Cat.Category

module Cat.Functors.Compose {{A B C : Category}} where

open import Cat.Functor

open Category {{…}}
open Functor

composeFunctor : Functor B C → Functor A B → Functor A C
composeFunctor G F = record
  { isFunctor = record
    { map = λ x → map G (map F x)
    ; ≃-map-id =
        begin
          map G (map F id)
        ≃⟨ ≃-map-cong G (≃-map-id F) ⟩
          map G id
        ≃⟨ ≃-map-id G ⟩
          id
        ∎
    ; ≃-map-∘ = λ {_}{_}{_} {f} {g} →
        begin
          map G (map F g) ∘ map G (map F f)
        ≃⟨ ≃-map-∘ G ⟩
          map G (map F g ∘ map F f)
        ≃⟨ ≃-map-cong G (≃-map-∘ F) ⟩
          map G (map F (g ∘ f))
        ∎
    ; ≃-map-cong = λ p → ≃-map-cong G (≃-map-cong F p)
    }
  }

infixr 90 _⊚_
_⊚_ = composeFunctor
