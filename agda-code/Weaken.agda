open import lib
open import VarInterface

module Weaken(vi : VI) where

open VI vi
open import Ctxt vi
open import Tm vi

data Weaken : ∀{Γ1 Γ Γ2 : Ctxt} → Tm (Γ1 ++ Γ2) → Tm (Γ1 ++ Γ ++ Γ2) → Set where
 weakenVar : ∀{Γ1 Γ Γ2 : Ctxt}{v : V}
              (i : inCtxt v (Γ1 ++ Γ2)) →
              (a : v # Γ) →
              Weaken{Γ1}{Γ}{Γ2} (var v i) (var v (inCtxtWeaken{Γ1} i a))
 weakenApp : ∀{Γ1 Γ Γ2 : Ctxt} → 
              {t1 t2 : Tm (Γ1 ++ Γ2)}
              {t1' t2' : Tm (Γ1 ++ Γ ++ Γ2)} →
              Weaken{Γ1} t1 t1' →
              Weaken{Γ1} t2 t2' →                
              Weaken{Γ1} (t1 · t2) (t1' · t2')
 weakenLam : ∀{Γ1 Γ Γ2 : Ctxt}{x : V} →
              {t : Tm (x :: Γ1 ++ Γ2)}
              {t' : Tm (x :: Γ1 ++ Γ ++ Γ2)} →
              Weaken{x :: Γ1} t t' →
              Weaken{Γ1} (ƛ x t) (ƛ x t')

weakenDeterministic : ∀{Γ1 Γ Γ2 : Ctxt}{t1 : Tm (Γ1 ++ Γ2)}{t2 t2' : Tm (Γ1 ++ Γ ++ Γ2)} →
                       Weaken{Γ1} t1 t2 →
                       Weaken{Γ1} t1 t2' →
                       t2 ≡ t2'
weakenDeterministic (weakenVar i a) (weakenVar .i a') rewrite #-deterministic a a' = refl
weakenDeterministic (weakenApp w1 w2) (weakenApp w1' w2') rewrite weakenDeterministic w1 w1' | weakenDeterministic w2 w2' = refl
weakenDeterministic (weakenLam w) (weakenLam w') rewrite weakenDeterministic w w'  = refl


{-



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


-}