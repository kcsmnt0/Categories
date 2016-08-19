open import Cat.Category
open import Cat.Bifunctor

open import Cat.Categories.Product renaming (productCategory to _×_)

module Cat.Functors.FromBifunctor {{A B C D}} (bifunctor : Bifunctor A B (C × D)) where

open import Cat.Functor

open import Cat.Setoids.Product using (_,_; fst; snd)

open Bifunctor bifunctor
open Category {{…}}

instance
  fstFunctor : Bifunctor A B (C × B)
  fstFunctor = record
    { transport = λ ab → fst (bitransport ab) , snd ab
    ; isFunctor = record
      { map = λ fg → fst (bimap fg) , snd fg
      ; ≃-map-id = fst ≃-bimap-id , refl
      ; ≃-map-∘ = fst ≃-bimap-∘ , refl
      ; ≃-map-cong = λ pq → fst (≃-bimap-cong pq) , snd pq
      }
    }

  sndFunctor : Bifunctor A B (A × D)
  sndFunctor = record
    { transport = λ ab → fst ab , snd (bitransport ab)
    ; isFunctor = record
      { map = λ fg → fst fg , snd (bimap fg)
      ; ≃-map-id = refl , snd ≃-bimap-id
      ; ≃-map-∘ = refl , snd ≃-bimap-∘
      ; ≃-map-cong = λ pq → fst pq , snd (≃-bimap-cong pq)
      }
    }
