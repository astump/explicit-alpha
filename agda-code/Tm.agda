open import lib
open import VarInterface

module Tm where

data Tm : Set where
  var : V → Tm 
  _·_ : (t1 t2 : Tm) → Tm 
  ƛ : (x : V) → (t : Tm) → Tm 

infixl 10 _·_ 
infixl 9 ƛ

-- generate a variable different from all others in the given Tm, as well as the given one
freshFor : V → Tm → V
freshFor v (var x) = fresh2 v x 
freshFor v (t1 · t2) = freshFor (freshFor v t1) t2
freshFor v (ƛ x t) = freshFor (fresh2 v x) t

fvs : Tm → 𝕃 V
fvs (var x) = [ x ]
fvs (t1 · t2) = fvs t1 ++ fvs t2
fvs (ƛ x t) = remove _≃_ x (fvs t)

vars : Tm → 𝕃 V
vars (var x) = [ x ]
vars (t · t₁) = vars t ++ vars t₁
vars (ƛ x t) = x :: vars t