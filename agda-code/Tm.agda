open import lib
open import VarInterface

module Tm(vi : VI) where

open VI vi
open import Ctxt vi

data Tm : Ctxt → Set where
  var : {Γ : Ctxt}(x : V)(i : inCtxt x Γ) → Tm Γ
  _·_ : {Γ : Ctxt}(t : Tm Γ) → (t' : Tm Γ) → Tm Γ
  ƛ : {Γ : Ctxt}(x : V) → (t : Tm (x :: Γ)) → Tm Γ

infixl 10 _·_ 
infixl 9 ƛ

