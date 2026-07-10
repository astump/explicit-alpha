open import lib
open import VarInterface

module Substitution where

open import Tm

Substitution : Set
Substitution = 𝕃 (V × Tm)
infix 6 [_/_]_
[_/_]_ : Tm → V → Substitution → Substitution
[ t / v ] σ = (v , t) :: σ

lookup : Substitution → V → maybe Tm
lookup [] x = nothing
lookup ((y , t) :: σ) x = if x ≃ y then just t else lookup σ x

subst-var : Substitution → V → Tm
subst-var σ x with lookup σ x 
subst-var σ x | nothing = var x
subst-var σ x | just t = t

var-mapped : V → Substitution → 𝔹
var-mapped _ [] = ff
var-mapped x ((y , t) :: σ) = x ≃ y || var-mapped x σ


lookup-nothing : ∀{σ : Substitution}{x : V} →
                  lookup σ x ≡ nothing →
                  subst-var σ x ≡ var x
lookup-nothing{σ}{x} e with (lookup σ x)
lookup-nothing {_} {_} e | nothing = refl

lookup-just : ∀{σ : Substitution}{x : V}{t : Tm} →
                  lookup σ x ≡ just t →
                  subst-var σ x ≡ t
lookup-just{σ}{x} e with lookup σ x
lookup-just {σ} {x} refl | just x₁ = refl

