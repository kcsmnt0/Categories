module Cat.Quivers.Pullback where

data V : Set where
  α β γ : V

data _▸_ : V → V → Set where
  φ : α ▸ β
  ψ : γ ▸ β
