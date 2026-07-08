open import lib
open import VarInterface

module Subst where

open import Tm 
open import Ctxt
open import Apart
open import Substitution

data Subst : Ctxt → Substitution → Tm → Tm → Set where
  var-found : ∀{Γ : Ctxt}{σ : Substitution}{v : V}{t : Tm} → 
                  lookup σ v ≡ just t → 
                  Apart t Γ → 
                  Subst Γ σ (var v) t
  var-not : ∀{Γ : Ctxt}{σ : Substitution}{v : V} → 
                  lookup σ v ≡ nothing → 
                  Subst Γ σ (var v) (var v)
  app : ∀{Γ : Ctxt}{σ : Substitution}
              {t1 t2 t1' t2' : Tm} → 
              Subst Γ σ t1 t1' →
              Subst Γ σ t2 t2' →
              Subst Γ σ (t1 · t2) (t1' · t2')
  lam : ∀{Γ : Ctxt}{σ : Substitution}{x : V}
              {t t' : Tm} → 
              Subst (x :: Γ) σ t t' →
              Subst Γ σ (ƛ x t) (ƛ x t')

Subst-refl : ∀{Γ : Ctxt}{t : Tm} →
             Subst Γ [] t t
Subst-refl {Γ} {var x} = var-not refl
Subst-refl {Γ} {t · t₁} = app Subst-refl Subst-refl
Subst-refl {Γ} {ƛ x t} = lam Subst-refl

{-
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

-}