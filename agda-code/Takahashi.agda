{- The function proposed by Takahashi to compute the maximum
   parallel reduct of t.
-}
open import lib hiding (_>>=_ ; return ; _∘_)
open import relations
open import diamond
open import VarInterface
open import Monad

module Takahashi where

open import Tm 
open import Substitution

αc : Tm → 𝕃 V → Tm
αc (var x) _ = var x
αc (t1 · t2) vs = αc t1 vs · αc t2 vs
αc (ƛ x t) vs =
  let n = fresh vs in
    ƛ n (graft1 (var n) x (αc t (n :: vs)))



tk : Tm → Tm
tk (var x) = var x
tk (var x · t) = var x · tk t
tk ((t1 · t2) · t3) = (tk (t1 · t2)) · tk t3
tk ((ƛ x t1) · t2) = graft1 (tk t2) x (tk t1)
tk (ƛ x t) = ƛ x (tk t)

varDiff : Tm → 𝕃 V → 𝔹
varDiff (var x) vs = list-member _≃_ x vs
varDiff (t1 · t2) vs = varDiff t1 vs && varDiff t2 vs
varDiff (ƛ x t) vs = ~ list-member _≃_ x vs && varDiff t (x :: vs)

{-
varDiff-rename : ∀{t : Tm}{ρ : Renaming}{vs : 𝕃 V} → 
                  idempotentr ρ ≡ tt → 
                  varDiff (αc t (domr ρ ++ vs)) (domr ρ ++ vs) ≡ tt →
                  varDiff (graft (↑ ρ) (αc t (ranr ρ ++ vs))) (ranr ρ ++ vs) ≡ tt
varDiff-rename {var x} {ρ} {vs} i d = {!!}
varDiff-rename {t1 · t2} {ρ} {vs} i d = {!!}
varDiff-rename {ƛ x t} {ρ} {vs} i d = {!!}



  varDiff (αc (ƛ x t) (domr ρ ++ vs)) (domr ρ ++ vs) ≡ tt →
  varDiff (graft (↑ ρ) (αc (ƛ x t) (ranr ρ ++ vs))) (ranr ρ ++ vs) ≡ tt


varDiff-rename1 : ∀{t : Tm}{x y : V}{vs : 𝕃 V} →
                  varDiff (αc t (x :: vs)) (x :: vs) ≡ tt →
                  varDiff (graft1 (var y) x (αc t (y :: vs))) (y :: vs) ≡ tt
varDiff-rename1 {var z} {x} {y} {vs} d = {!!}
varDiff-rename1 {t1 · t2} {x} {y} {vs} d = {!!}
varDiff-rename1 {ƛ z t} {x} {y} {vs} d rewrite fresh-distinct{y :: vs} =
-- let p = varDiff-rename1{t}{x}{y}
{!!}
-}



varDiff-rename1 : ∀{t : Tm}{x : V}{vs : 𝕃 V} →
                  isSublist (fvs t) (x :: vs) _≃_ ≡ tt → 
                  varDiff (αc t (x :: vs)) (x :: vs) ≡ tt →
                  let n = fresh vs in
                  let vs' = n :: vs in
                   varDiff (graft1 (var n) x (αc t vs')) vs' ≡ tt
varDiff-rename1 {var y} {x} {vs} sl d = {!!}
varDiff-rename1 {t1 · t2} {x} {vs} sl d = {!!}
varDiff-rename1 {ƛ y t} {x} {vs} sl d = {!!}


αc-varDiff : ∀{t : Tm}{vs : 𝕃 V} →
             isSublist (fvs t) vs _≃_ ≡ tt → 
             varDiff (αc t vs) vs ≡ tt
αc-varDiff {var x} {vs} sl = &&-elim1 sl
αc-varDiff {t1 · t2} {vs} sl rewrite αc-varDiff {t1} {vs} (isSublist-++1l{eq = _≃_}{fvs t1}{fvs t2}{vs} sl)
                                   | αc-varDiff {t2} {vs} ((isSublist-++2l{eq = _≃_}{fvs t1}{fvs t2}{vs} sl)) = refl
αc-varDiff {ƛ x t} {vs} sl rewrite fresh-distinct{vs} =
  let q = isSublist-remove{eq = _≃_}{fvs t}{vs} (λ{a} → ≃-sym{a}) sl in
  let p = αc-varDiff{t}{x :: vs} q in
    varDiff-rename1 {t} {x} {vs} q p
