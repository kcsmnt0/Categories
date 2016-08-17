open import Cat.Category
open import Cat.Functor

open import Cat.Categories.Setoid

module Cat.Representable {{C}} (F : Functor C setoidCategory) (r : [ C ]) where

open import Cat.NaturalIsomorphism
open import Cat.Setoid

open import Cat.Functors.Hom

IsRepresentable = NaturalIsomorphism (homFunctor r) F
