open import lib
open import VarInterface

module Substitution where

open import Tm
open import Ctxt
open import Apart 

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

-- capture is allowed
graft : Substitution → Tm → Tm
graft σ (var x) = subst-var σ x
graft σ (t1 · t2) = graft σ t1 · graft σ t2
graft σ (ƛ x t) = ƛ x (graft σ t)

infix 5 _∉subst_

_∉subst_ : V → Substitution → Set
v ∉subst σ = all-pred (λ p → v ∉ (snd p)) σ

subst-Apart : Substitution → Ctxt → Set
subst-Apart σ Γ = all-pred (λ p → Apart (snd p) Γ) σ

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
{-
subst-Apart-var : ∀{x : V}{Γ : Ctxt}{σ : Substitution} →
                  subst-Apart σ Γ →
                  Apart (subst-var σ x) Γ
subst-Apart-var {x} {Γ} {[]} a = {!!}
subst-Apart-var {x} {Γ} {x₁ :: σ} a = {!!}
-}

redexes : Substitution → Tm → Tm
redexes [] t = t
redexes ((x , t1) :: σ) t2 = (ƛ x (redexes σ t2)) · t1

-- the free variables in the range are apart from the domain of the substitution
idempotent : Substitution → Set
idempotent σ = subst-Apart σ (map fst σ)