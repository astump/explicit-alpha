open import lib
open import VarInterface

module Apart(vi : VI) where

open VI vi
open import Ctxt vi
open import Tm vi

data Apart : Tm → Ctxt → Set where
 apartVar : ∀{Γ : Ctxt}{v : V}
             (a : v # Γ) →
             Apart (var v) Γ
 apartApp : ∀{Γ : Ctxt}
             {t1 t2 : Tm} → 
             Apart t1 Γ →
             Apart t2 Γ →              
             Apart (t1 · t2) Γ
 apartLam : ∀{Γ : Ctxt}{x : V} 
             {t : Tm} → 
             Apart t (ctxtDrop x Γ) →
             Apart (ƛ x t) Γ

