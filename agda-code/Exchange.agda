open import lib
open import VarInterface

module Exchange(vi : VI) where

open VI vi
open import Ctxt vi
open import Tm vi

data Exchange : ∀{Γ'' Γ' Γ : Ctxt}{x : V} →
                 Tm (Γ'' ++ Γ' ++ x :: Γ) → 
                 Tm (Γ'' ++ x :: Γ' ++ Γ) →
                 Set where
  exchangeVar : ∀{Γ'' Γ' Γ : Ctxt}{x v : V}
                 (i : inCtxt v (Γ'' ++ Γ' ++ x :: Γ')) →
                 (a : x # Γ') →
                 Exchange{Γ''} (var v i) (var v (inCtxtExchange{Γ'' = Γ''} i a))
  exchangeApp : ∀{Γ'' Γ' Γ : Ctxt}{x : V} → 
                 {t1 t2 : Tm (Γ'' ++ Γ' ++ x :: Γ)} →
                 {t1' t2' : Tm (Γ'' ++ x :: Γ' ++ Γ)} →
                 Exchange t1 t1' →
                 Exchange t2 t2' →                 
                 Exchange (t1 · t2) (t1' · t2')
  exchangeLam : ∀{Γ'' Γ' Γ : Ctxt}{x y : V} → 
                 {t : Tm (y :: Γ'' ++ Γ' ++ x :: Γ)} →
                 {t' : Tm (y :: Γ'' ++ x :: Γ' ++ Γ)} →
                 Exchange{y :: Γ''} t t' → 
                 Exchange (ƛ y t) (ƛ y t') 

exchangeTriv : ∀{Γ' Γ : Ctxt}{x : V}{t t' : Tm (Γ' ++ x :: Γ)} →
               Exchange{Γ' = []} t t' →
               t ≡ t'
exchangeTriv (exchangeVar i #empty) rewrite inCtxtExchangeTriv i = refl
exchangeTriv (exchangeApp e1 e2) rewrite exchangeTriv e1 | exchangeTriv e2 = refl
exchangeTriv (exchangeLam e) rewrite exchangeTriv e = refl

exchangeDeterministic : ∀{Γ'' Γ' Γ : Ctxt}{x : V} 
                         {t : Tm (Γ'' ++ Γ' ++ x :: Γ)}
                         {t1 : Tm (Γ'' ++ x :: Γ' ++ Γ)} →
                         {t2 : Tm (Γ'' ++ x :: Γ' ++ Γ)} →                          
                         Exchange t t1 →
                         Exchange t t2 →                         
                         t1 ≡ t2
exchangeDeterministic (exchangeVar i a) (exchangeVar .i a') rewrite #-deterministic a a' = refl
exchangeDeterministic (exchangeApp e1 e2) (exchangeApp e1' e2') rewrite exchangeDeterministic e1 e1' | exchangeDeterministic e2 e2' = refl
exchangeDeterministic (exchangeLam e) (exchangeLam e') rewrite exchangeDeterministic e e' = refl