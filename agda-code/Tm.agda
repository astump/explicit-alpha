open import lib
open import VarInterface

module Tm(vi : VI) where

open VI vi 
open import VarOps vi

data Tm : Set where
  var : V → Tm 
  _·_ : (t1 t2 : Tm) → Tm 
  ƛ : (x : V) → (t : Tm) → Tm 

infixl 9 _·_ 
infixl 8 ƛ

fvs : Tm → 𝕃 V
fvs (var x) = [ x ]
fvs (t1 · t2) = fvs t1 ++ fvs t2
fvs (ƛ x t) = varrem x (fvs t)

infix 8 _∈_

-- x ∈ t means x occurs free in t
_∈_ : V → Tm → 𝔹
x ∈ t = varmem x (fvs t)

bvs : Tm → 𝕃 V
bvs (var x) = []
bvs (t · t₁) = bvs t ++ bvs t₁ 
bvs (ƛ x t) = x :: bvs t

size : Tm → ℕ
size (var x) = 1
size (t1 · t2) = suc (size t1 + size t2)
size (ƛ x t) = suc (size t)

