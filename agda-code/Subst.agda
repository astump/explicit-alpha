open import lib
open import VarInterface

module Subst(vi : VI) where

open VI vi
open import Tm vi
open import Ctxt vi
open import Apart vi

data Subst : Ctxt → Tm → V → Tm → Tm → Set where
  substVarFound : ∀{Γ : Ctxt}{t : Tm}{v : V} → 
                  Apart t Γ → 
                  Subst Γ t v (var v) t
  substVarNot : ∀{Γ : Ctxt}{t : Tm}{v v' : V}
                 (a : v ≃ v' ≡ ff) → 
                 Subst Γ t v (var v') (var v')
  substApp : ∀{Γ : Ctxt}{t : Tm}{v : V}
              {t1 t2 t1' t2' : Tm} → 
              Subst Γ t v t1 t1' →
              Subst Γ t v t2 t2' →
              Subst Γ t v (t1 · t2) (t1' · t2')
  substLam : ∀{Γ : Ctxt}{t : Tm}{v x : V}
              {t t' : Tm} → 
              Subst (x :: Γ) t v t t' →
              Subst Γ t v (ƛ x t) (ƛ x t')

substDeterministic : ∀{Γ : Ctxt}
                      {t1 : Tm}
                      {v : V}
                      {t2 r1 r2 : Tm} → 
                      Subst Γ t1 v t2 r1 →
                      Subst Γ t1 v t2 r2 →
                      r1 ≡ r2
substDeterministic (substVarFound x) (substVarFound x₁) = refl
substDeterministic{v = v} (substVarFound x) (substVarNot a) rewrite ≃-refl {v} with a
substDeterministic (substVarFound x) (substVarNot a) | ()
substDeterministic{v = v} (substVarNot a) (substVarFound x) rewrite ≃-refl {v} with a
substDeterministic (substVarNot a) (substVarFound x) | ()
substDeterministic (substVarNot a) (substVarNot a₁) = refl
substDeterministic (substApp s1 s2) (substApp s1' s2') rewrite substDeterministic s1 s1' | substDeterministic s2 s2' = refl
substDeterministic (substLam s) (substLam s') rewrite substDeterministic s s' = refl