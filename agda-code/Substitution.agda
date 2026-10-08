open import lib hiding (_∘_)
open import VarInterface

module Substitution(vi : VI) where

open VI vi

open import Tm vi
open import VarOps vi
open import Apart vi

Substitution : Set
Substitution = 𝕃 (V × Tm)
infix 6 [_/_]_
[_/_]_ : Tm → V → Substitution → Substitution
[ t / v ] σ = (v , t) :: σ

lookup : Substitution → V → maybe Tm
lookup [] x = nothing
lookup ((y , t) :: σ) x = if x ≃ y then just t else lookup σ x

infix 7 _\\_
_\\_ : Substitution → V → Substitution
[] \\ _ = []
((x , t) :: σ) \\ y = if x ≃ y then σ \\ y else (x , t) :: (σ \\ y)

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
graft σ (ƛ x t) = ƛ x (graft (σ \\ x) t)

graft1 : Tm → V → Tm → Tm
graft1 t2 y t1 = graft [ y , t2 ] t1

subst-Apart : Substitution → 𝕃 V → 𝔹
subst-Apart σ Γ = list-all (λ p → Apart (snd p) Γ) σ

dom : Substitution → 𝕃 V
dom = map fst


-- the free variables in the range are apart from the domain of the substitution
idempotent : Substitution → 𝔹
idempotent σ = subst-Apart σ (dom σ)

infixl 7 _∘_ 

-- composition of substitutions by grafting into the range of the first one
_∘_ : Substitution → Substitution → Substitution
[] ∘ σ' = []
((x , t) :: σ) ∘ σ' = (x , graft σ' t) :: σ ∘ σ'

in-dom : V → Substitution → 𝔹
in-dom x σ = list-member _≃_ x (dom σ)   

