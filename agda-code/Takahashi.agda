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

αtk-∘-var : ∀ {x : V}{σ σ' : Substitution} →
            in-dom x σ ≡ tt → 
            subst-var (σ ∘ σ') x ≡ graft σ' (subst-var σ x)
αtk-∘-var {x} {[]} {σ'} ()
αtk-∘-var {x} {(y , t) :: σ} {σ'} m with x =ℕ y 
αtk-∘-var {x} {(y , t) :: σ} {σ'} m | tt = refl
αtk-∘-var {x} {(y , t) :: σ} {σ'} m | ff with lookup-mem{x}{σ} m
αtk-∘-var {x} {(y , t) :: σ} {σ'} m | ff | r , eq rewrite eq | lookup-∘-just{x}{σ}{σ'}{r} eq = refl

αtk-∘ : ∀ {t : Tm}{vs : 𝕃 V}{σ σ' : Substitution} →
          isSublist (dom σ') vs _≃_ ≡ tt → 
          isSublist (fvs t) (dom σ) _≃_ ≡ tt → 
          αtk t vs (σ ∘ σ') ≡ graft σ' (αtk t vs σ) 
αtk-∘ {var x} {vs} {σ} {σ'} _ sl = αtk-∘-var{x}{σ}{σ'} h
 where h : in-dom x σ ≡ tt
       h rewrite &&-tt (in-dom x σ) = sl

αtk-∘ {ta · tb} {vs} {σ} {σ'} dl sl with αtk-∘{ta}{vs}{σ}{σ'} dl (isSublist-++1l{eq = _≃_}{fvs ta}{fvs tb}{dom σ} sl)
                                       | αtk-∘{tb}{vs}{σ}{σ'} dl (isSublist-++2l{eq = _≃_}{fvs ta}{fvs tb}{dom σ} sl)
αtk-∘ {var x · t2} {vs} {σ} {σ'} dl sl | p1 | p2 rewrite p2 | αtk-∘-var{x}{σ}{σ'} (&&-elim1 sl) = refl

αtk-∘ {t1 · t2 · t3} {vs} {σ} {σ'} dl sl | p1 | p2 rewrite p1 | p2 = refl
--isSublist (remove _=ℕ_ y (fvs t1) ++ fvs t2) (dom σ) _≃_ ≡ tt
αtk-∘ {(ƛ y t1) · t2} {vs} {σ} {σ'} dl sl | p1 | p2 rewrite p2
  | list-all-append (λ a → list-member _≃_ a (dom σ))(filter (λ x → ~ y =ℕ x) (fvs t1)) (fvs t2) =
  αtk-∘ {t1} {vs} dl (isSublist-remove {l1 = fvs t1}{dom σ}{y} (λ{a}{b} → λ x → ≃-sym{a}{b} x) (&&-elim1 sl )) 

αtk-∘ {ƛ x t} {vs} {σ} {σ'} dl sl with αtk-∘{t}{fresh-ℕ vs :: vs}{(x , var (fresh-ℕ vs)) :: σ}{σ'}
           ((isSublist-++2{eq = _≃_}{[ fresh-ℕ vs ]}{dom σ'}{vs} (λ{x} → ≃-refl{x}) dl))
           ((isSublist-remove{l1 = fvs t}{dom σ}{x} (λ{a}{b} → λ x → ≃-sym{a}{b} x) sl))
           | subst-var-not-member{fresh vs}{σ'} (list-member-sub-ff{eq = _≃_}{fresh vs}{dom σ'}{vs} =ℕ-to-≡ dl (fresh-distinct{vs}))
αtk-∘ {ƛ x t} {vs} {σ} {σ'} dl sl | p | eq rewrite eq | p = refl

αtk-++ :
  ∀{s : Tm}{vs : 𝕃 V}{σ1 σ2 σ3 : Substitution} → 
    αtk s vs (σ1 ++ σ2 ++ σ3) ≡ graft σ2 (αtk s vs (σ1 ++ σ3))
αtk-++ {var x} {vs} {σ1} {σ2} {σ3} = {!!}
αtk-++ {var x · s} {vs} {σ1} {σ2} {σ3} = {!!}
αtk-++ {s1 · s2 · s3} {vs} {σ1} {σ2} {σ3} = {!!}
αtk-++ {(ƛ x s1) · s2} {vs} {σ1} {σ2} {σ3} rewrite αtk-++{s1}{vs}{(x , αtk s2 vs (σ1 ++ σ2 ++ σ3)) :: σ1}{σ2}{σ3}
 | αtk-++{s2}{vs}{σ1}{σ2}{σ3} = {!!}
αtk-++ {ƛ x s} {vs} {σ1} {σ2} {σ3} = {!!}