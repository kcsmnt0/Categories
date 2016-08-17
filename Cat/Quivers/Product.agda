{-# OPTIONS --type-in-type #-}

module Cat.Quivers.Product where

data V : Set where
  α β : V

transport : ∀ {A} a b → V → A
transport a b α = a
transport a b β = b

data _▸_ : V → V → Set where

map : ∀ {A} {x y} → x ▸ y → A
map ()
