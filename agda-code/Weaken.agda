open import lib
open import VarInterface

module Weaken(vi : VI) where

open VI vi
open import Ctxt vi
open import Tm vi
open import Exchange vi

data Weaken : ∀{Γ' Γ : Ctxt} → Tm Γ → Tm (Γ' ++ Γ) → Set where
  weakenVar : ∀{Γ' Γ : Ctxt}{v : V}
               (i : inCtxt v Γ) →
               (a : v # Γ') →
               Weaken (var v i) (var v (inCtxt++ i a))
  weakenApp : ∀{Γ' Γ : Ctxt} → 
               {t1 t2 : Tm Γ}
               {t1' t2' : Tm (Γ' ++ Γ)} →
               Weaken t1 t1' →
               Weaken t2 t2' →                
               Weaken (t1 · t2) (t1' · t2')
  weakenLam : ∀{Γ' Γ : Ctxt}{x : V} →
               {t : Tm (x :: Γ)}
               {t' : Tm (Γ' ++ x :: Γ)}
               {t'' : Tm (x :: Γ' ++ Γ)} →
               Weaken t t' →
               Exchange{[]} t' t'' →               
               Weaken (ƛ x t) (ƛ x t'')


weakenTriv : ∀{Γ : Ctxt}{t t' : Tm Γ} →
              Weaken t t' →
              t ≡ t'
weakenTriv (weakenVar i a) = refl
weakenTriv (weakenApp w1 w2) rewrite weakenTriv w1 | weakenTriv w2 = refl
weakenTriv (weakenLam w x) rewrite exchangeTriv x | weakenTriv w = refl

weakenTrivSym : ∀{Γ : Ctxt}{t t' : Tm Γ} →
                Weaken t t' →
                Weaken t' t
weakenTrivSym w with weakenTriv w
weakenTrivSym w | refl = w

weakenDeterministic : ∀{Γ' Γ : Ctxt}{t1 : Tm Γ}{t2 t2' : Tm (Γ' ++ Γ)} →
                       Weaken t1 t2 →
                       Weaken t1 t2' →
                       t2 ≡ t2'
weakenDeterministic (weakenVar i a) (weakenVar .i a') rewrite #-deterministic a a' = refl
weakenDeterministic (weakenApp w1 w2) (weakenApp w1' w2') rewrite weakenDeterministic w1 w1' | weakenDeterministic w2 w2' = refl
weakenDeterministic (weakenLam w x) (weakenLam w' x') rewrite weakenDeterministic w w' | exchangeDeterministic x x' = refl