open import lib
open import VarInterface

module Subst(vi : VI) where

open VI vi
open import Tm vi
open import Ctxt vi
open import Weaken vi


data Subst : ∀{Γ' Γ : Ctxt} → Tm Γ → (v : V) → Tm (Γ' ++ v :: Γ) → Tm (Γ' ++ Γ) → Set where
  substVarFound : ∀{Γ' Γ : Ctxt}{t : Tm Γ}{t' : Tm (Γ' ++ Γ)}{v : V}
                  (a : v # Γ') →
                  Weaken t t' → 
                  Subst t v (var v (inCtxt++ foundInCtxt a)) t'
  substVarNot : ∀{Γ' Γ : Ctxt}{t : Tm Γ}{v v' : V}
                  (a : v ≃ v' ≡ ff)
                  (i : inCtxt v' (Γ' ++ v :: Γ)) → 
                  Subst t v (var v' i) (var v' (strengthenCtxt i a))
  substApp : ∀{Γ' Γ : Ctxt}{t : Tm Γ}{v : V}
              {t1 t2 : Tm (Γ' ++ v :: Γ)}
              {t1' t2' : Tm (Γ' ++ Γ) } → 
              Subst t v t1 t1' →
              Subst t v t2 t2' →
              Subst t v (t1 · t2) (t1' · t2')
  substLam : ∀{Γ' Γ : Ctxt}{t : Tm Γ}{v x : V}
              {t1 : Tm (x :: Γ' ++ v :: Γ)}
              {t1' : Tm (x :: Γ' ++ Γ)} → 
              Subst t v t1 t1' →
              Subst t v (ƛ x t1) (ƛ x t1')

substDeterministic : ∀{Γ Γ' : Ctxt}
                       {t1 : Tm Γ}
                       {v : V}
                       {t2 : Tm (Γ' ++ v :: Γ)}
                       {r1 r2 : Tm (Γ' ++ Γ)} →
                       Subst t1 v t2 r1 →
                       Subst t1 v t2 r2 →
                       r1 ≡ r2
substDeterministic{Γ}{v = v} (substVarFound a x) s' with inCtxt++{Γ = v :: Γ} foundInCtxt a 
substDeterministic {_} {v = _} (substVarFound a x) (substVarFound a₁ x') | .(inCtxt++ foundInCtxt a₁) = weakenDeterministic x x'
substDeterministic {_} {v = v} (substVarFound a x) (substVarNot a₁ .i) | i with trans (sym a₁) (≃-refl{v})
substDeterministic {_} {v = v} (substVarFound a x) (substVarNot a₁ .i) | i | ()
substDeterministic {v = v} (substVarNot a .(inCtxt++ foundInCtxt a₁)) (substVarFound a₁ x) with trans (sym a) (≃-refl{v}) 
substDeterministic {v = v} (substVarNot a .(inCtxt++ foundInCtxt a₁)) (substVarFound a₁ x) | ()
substDeterministic (substVarNot a i) (substVarNot a₁ .i) rewrite ≃-uip a a₁ = refl 
substDeterministic (substApp s1 s2) (substApp s1' s2') rewrite substDeterministic s1 s1' | substDeterministic s2 s2' = refl
substDeterministic (substLam s) (substLam s') rewrite substDeterministic s s' = refl


weakenSubst : ∀{Γ' Γ : Ctxt}{t : Tm Γ}{x : V}{t' : Tm (Γ' ++ x :: Γ)}{r : Tm (Γ' ++ Γ)} →
               Subst t x t' r →
               Σ[ w ∈ Tm (x :: Γ' ++ Γ) ]  (Weaken{[ x ]} r w)
weakenSubst (substVarFound a x) = {!!}
weakenSubst (substVarNot a i) = {!!}
weakenSubst (substApp s1 s2) = {!!}
weakenSubst (substLam s) = {!!}