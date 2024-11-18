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
 