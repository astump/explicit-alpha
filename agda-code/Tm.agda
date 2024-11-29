open import lib
open import VarInterface

module Tm(vi : VI) where

open VI vi

data Tm : Set where
  var : V → Tm 
  _·_ : (t1 t2 : Tm) → Tm 
  ƛ : (x : V) → (t : Tm) → Tm 

infixl 10 _·_ 
infixl 9 ƛ

