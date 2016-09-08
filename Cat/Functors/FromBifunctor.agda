open import Cat.Category
open import Cat.Bifunctor

open import Cat.Categories.Product renaming (productCategory to _×_)

module Cat.Functors.FromBifunctor {{A B C}} (bifunctor : Bifunctor A B C) where

open import Cat.Functor

open import Cat.Setoids.Product using (_,_; fst; snd)

open Bifunctor bifunctor
open Category {{…}}

fstFunctor : [ B ] → Functor A C
fstFunctor b = record
  { transport = λ a → bitransport (a , b)
  ; isFunctor = record
    { map = λ f → bimap (f , id)
    ; ≃-map-id = ≃-bimap-id
    ; ≃-map-∘ = trans ≃-bimap-∘ (≃-bimap-cong (refl , idUnitᴸ))
    ; ≃-map-cong = λ p → ≃-bimap-cong (p , refl)
    }
  }

sndFunctor : [ A ] → Functor B C
sndFunctor a = record
  { transport = λ b → bitransport (a , b)
  ; isFunctor = record
    { map = λ g → bimap (id , g)
    ; ≃-map-id = ≃-bimap-id
    ; ≃-map-∘ = trans ≃-bimap-∘ (≃-bimap-cong (idUnitᴸ , refl))
    ; ≃-map-cong = λ q → ≃-bimap-cong (refl , q)
    }
  }
