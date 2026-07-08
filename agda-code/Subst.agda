open import lib
open import VarInterface

module Subst where

open import Tm 
open import Ctxt
open import Apart
open import Substitution

data Subst : Substitution → Tm → Tm → Set where
  var : ∀{σ : Substitution}{v : V} → 
           Subst σ (var v) (subst-var σ v)
  app : ∀{σ : Substitution}
         {t1 t2 t1' t2' : Tm} → 
         Subst σ t1 t1' →
         Subst σ t2 t2' →
         Subst σ (t1 · t2) (t1' · t2')
  lam : ∀{σ : Substitution}{x : V}{t t' : Tm} →
         x ∉ran σ → 
         Subst σ t t' →
         Subst σ (ƛ x t) (ƛ x t')

Subst-refl : ∀{t : Tm} →
             Subst [] t t
Subst-refl {var x} = var 
Subst-refl {t · t₁} = app Subst-refl Subst-refl
Subst-refl {ƛ x t} = lam triv Subst-refl

{-
substDeterministic : ∀
                      {t1 : Tm}
                      {v : V}
                      {t2 r1 r2 : Tm} → 
                      Subst t1 v t2 r1 →
                      Subst t1 v t2 r2 →
                      r1 ≡ r2
substDeterministic (substVarFound x) (substVarFound x₁) = refl
substDeterministic{v = v} (substVarFound x) (substVarNot a) rewrite ≃-refl {v} with a
substDeterministic (substVarFound x) (substVarNot a) | ()
substDeterministic{v = v} (substVarNot a) (substVarFound x) rewrite ≃-refl {v} with a
substDeterministic (substVarNot a) (substVarFound x) | ()
substDeterministic (substVarNot a) (substVarNot a₁) = refl
substDeterministic (substApp s1 s2) (substApp s1' s2') rewrite substDeterministic s1 s1' | substDeterministic s2 s2' = refl
substDeterministic (substLam s) (substLam s') rewrite substDeterministic s s' = refl

-}