{- definition of parallel reduction, for proof of confluence.
-}
open import lib hiding (_>>=_ ; return )
open import relations
open import diamond
open import VarInterface

module Parallel where

open import Apart
open import Ctxt 
open import Tm 
open import Subst 
open import Takahashi 
open import Substitution 

infix 6 ⇒αβ_

data ⇒αβ_ : Substitution → Tm → Tm → Set where
  var : ∀{v : V}{σ : Substitution} → 
          var v ⟨ ⇒αβ σ ⟩ (subst-var σ v)
  app : ∀{t1 t2 t1' t2' : Tm}{σ : Substitution} →
        t1 ⟨ ⇒αβ σ ⟩ t1' →
        t2 ⟨ ⇒αβ σ ⟩ t2' →
        t1 · t2 ⟨ ⇒αβ σ ⟩ t1' · t2'
  beta : ∀{t1 : Tm}{x : V}{t2 : Tm}{t1' r : Tm}{σ : Substitution} →
        t1 ⟨ ⇒αβ σ ⟩ t1' →
        t2 ⟨ ⇒αβ ([ t1' / x ] σ) ⟩ r →
        (ƛ x t2) · t1 ⟨ ⇒αβ σ ⟩ r
  alpha : ∀{t t' : Tm}{x x' : V}{σ : Substitution} →
        t ⟨ ⇒αβ ([ var x' / x ] σ) ⟩ t' →
        x' ∉ t →                              -- avoid capture
        (ƛ x t) ⟨ ⇒αβ σ ⟩ (ƛ x' t')
  lam : ∀{t t' : Tm}{x : V}{σ : Substitution} →
        x ∉ran σ → 
        t ⟨ ⇒αβ σ ⟩ t' →
        ƛ x t ⟨ ⇒αβ σ ⟩ ƛ x t'

⇒αβ-refl : ∀{σ : Substitution}{t r : Tm} →
           Subst σ t r → 
           t ⟨ ⇒αβ σ ⟩ r
⇒αβ-refl {σ} {var x} {r} (var) = var  
⇒αβ-refl {σ} {t} {r} (app s1 s2) = app (⇒αβ-refl s1) (⇒αβ-refl s2)
⇒αβ-refl {σ} {t} {r} (lam u s) = lam u (⇒αβ-refl s)


data ⇒Args : Substitution → Substitution → Substitution → Set where
  arg-nil : ∀{σ : Substitution} → ⇒Args [] [] σ
  arg-cons : ∀{x : V}{s t : Tm}{σ1 σ2 σ : Substitution} →
              s ⟨ ⇒αβ (σ2 ++ σ) ⟩ t → 
              ⇒Args σ1 σ2 σ →
              ⇒Args ([ s / x ] σ1) ([ t / x ] σ2) σ



triangle-⇒αβ : ∀{σ1 σ2 σ : Substitution} →
               (a : ⇒Args σ1 σ2 σ) →
               ∀{s t : Tm} →
               s ⟨ ⇒αβ (σ2 ++ σ) ⟩ t →
               t ⟨ ⇒αβ [] ⟩ (αtk (redexes σ1 s) (fvs s) σ)
triangle-⇒αβ {σ1} {σ2} {σ} a {s} {t} var = {!!}
triangle-⇒αβ {σ1} {σ2} {σ} a {s} {t} (app x1 x2) = {!!}
triangle-⇒αβ {σ1} {σ2} {σ} a {(ƛ v s2) · s1} {t} (beta{t1' = t1} x1 x2) =
  let p = triangle-⇒αβ (arg-cons{v} x1 a) x2 in
    {!!}
triangle-⇒αβ {σ1} {σ2} {σ} a {s} {t} (alpha x1 x2) = {!!}
triangle-⇒αβ {σ1} {σ2} {σ} a {s} {t} (lam u x) = {!!}

