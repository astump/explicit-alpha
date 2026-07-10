{- The function proposed by Takahashi to compute the maximum
   parallel reduct of t.
-}
open import lib hiding (_>>=_ ; return )
open import relations
open import diamond
open import VarInterface
open import Monad

module Takahashi where

open import Tm 
open import Subst 
open import Substitution 

mutual 

 αtk-subst : Tm → V → Tm → 𝕃 V → Substitution → Tm
 αtk-subst s1 v s2 vs σ = αtk s2 vs ((v , αtk s1 vs σ) :: σ)

 αtk : Tm → 𝕃 V → Substitution → Tm
 αtk (var x) _ σ = subst-var σ x
 αtk (var x · t2) vs σ = (subst-var σ x) · αtk t2 vs σ
 αtk ((t1 · t2) · t3) vs σ = (αtk (t1 · t2) vs σ) · αtk t3 vs σ
 αtk (ƛ x t1 · t2) vs σ = αtk-subst t2 x t1 vs σ
 αtk (ƛ x t) vs σ =
  let q = fresh vs in
   ƛ q (αtk t (q :: vs) ((x , var q) :: σ))

{-
αtk-subst-var : ∀ {x : V}{s1 s2 : Tm}{vs : 𝕃 V} →
                var x ≡ αtk s2 vs [] → 
                αtk-subst s1 x s2 vs [] ≡ αtk s1 vs []
αtk-subst-var {x} {s1} {var x₁} {vs} refl rewrite =ℕ-refl x = refl
αtk-subst-var {x} {s1} {(ƛ y s2) · s3} {vs} e rewrite sym e = {!!}
-}