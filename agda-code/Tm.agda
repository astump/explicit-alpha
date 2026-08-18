open import lib
open import VarInterface

module Tm where

data Tm : Set where
  var : V → Tm 
  _·_ : (t1 t2 : Tm) → Tm 
  ƛ : (x : V) → (t : Tm) → Tm 

infixl 9 _·_ 
infixl 8 ƛ

fvs : Tm → 𝕃 V
fvs (var x) = [ x ]
fvs (t1 · t2) = fvs t1 ++ fvs t2
fvs (ƛ x t) = remove _≃_ x (fvs t)

infix 8 _∈_

-- x ∈ t means x occurs free in t
_∈_ : V → Tm → 𝔹
x ∈ t = varmem x (fvs t)

bvs : Tm → 𝕃 V
bvs (var x) = []
bvs (t · t₁) = bvs t ++ bvs t₁ 
bvs (ƛ x t) = x :: bvs t

∈var : ∀{x y : V}{b : 𝔹} →
       x ∈ var y ≡ b →
       x ≃ y ≡ b
∈var{x}{y}{b} eq with(x ≃ y)
∈var{x}{y}{b} eq | tt = eq
∈var{x}{y}{b} eq | ff = eq

∈· : ∀{x : V}{t1 t2 : Tm} →
     x ∈ t1 · t2 ≡ ff →
     x ∈ t1 ≡ ff ∧ x ∈ t2 ≡ ff
∈·{x}{t1}{t2} eq rewrite varmem-++ x (fvs t1)(fvs t2) = (||≡ff₁ eq) , (||≡ff₂ eq)