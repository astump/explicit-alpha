{- The function proposed by Takahashi to compute the maximum
   parallel reduct of t.
-}
open import lib hiding (_>>=_ ; return )
open import relations
open import diamond
open import VarInterface
open import Monad

module Takahashi where

open import Ctxt 
open import Tm 
open import Subst 
open import Substitution 


--
--  TkM should just be a Reader in the Substitution and set of variables
--



TkM : Set → Set
TkM A = 𝕃 V → Substitution → A
_>>=tk_ : ∀{A B : Set} → TkM A → (A → TkM B) → TkM B
_>>=tk_{A}{B} x f vs σ = f (x vs σ) vs σ

returntk : ∀{A : Set} → A → TkM A
returntk a vs σ = a 

instance
  TkMonad : Monad TkM
  TkMonad = record { return = returntk ; _>>=_ = _>>=tk_ }

getVars : TkM (𝕃 V)
getVars = λ vs σ → vs 

getSubstitution : TkM Substitution
getSubstitution = λ vs σ → σ 

withRenamed : ∀{A : Set} → V → (V → TkM A) → TkM A
withRenamed v f vs σ = let q = fresh vs in
                         f q (q :: vs) ((v , var q) :: σ)

withUpdatedSubst : ∀{A : Set} → V → Tm → TkM A → TkM A
withUpdatedSubst v t m vs σ = m vs ((v , t) :: σ)

subst-var-tk : V → TkM Tm
subst-var-tk v =
  do
    σ ← getSubstitution
    return (subst-var σ v)

mutual 

 αtk-subst : Tm → V → Tm → TkM Tm
 αtk-subst s2 v s1 = αtk s2 >>=tk (λ r2 → withUpdatedSubst v r2 (αtk s1))

 αtk : Tm → TkM Tm
 αtk (var x) = subst-var-tk x
 αtk (var x · t2) =
  do
    r1 ← subst-var-tk x
    r2 ← αtk t2
    return (r1 · r2)
 αtk ((t1 · t2) · t3) =
  do
    r1 ← αtk (t1 · t2)
    r2 ← αtk t3
    return (r1 · r2)
 αtk (ƛ x t1 · t2) = αtk-subst t2 x t1
 αtk (ƛ x t) =
  withRenamed x (λ q → 
    do
      r ← (αtk t)
      return (ƛ q r))


αtk-permute-redex : ∀{v : V}{s1 s2 : Tm}{σ1 σ : Substitution}{Γ : Ctxt} →
                    αtk (redexes ((v , s1) :: σ1) s2) Γ σ ≡ αtk (redexes (σ1 ++ [ v , s1 ]) s2) Γ σ
αtk-permute-redex {v} {s1} {s2} {[]} {σ} {Γ} = refl
αtk-permute-redex {v} {s1} {s2} {(v' , t) :: σ1} {σ} {Γ} with keep (αtk s1 Γ σ)
αtk-permute-redex {v} {s1} {s2} {(v' , t) :: σ1} {σ} {Γ} | r , eq rewrite eq = {!!}
