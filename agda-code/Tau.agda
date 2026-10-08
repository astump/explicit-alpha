open import lib
open import relations 
open import VarInterface

module Tau(vi : VI) where

open VI vi

open import Tm vi

data τ(r : Rel Tm) : Rel Tm where
 τ-base : ∀{t1 t2 : Tm} → t1 ⟨ r ⟩ t2 → t1 ⟨ τ r ⟩ t2
 τ-app1 : ∀{t1 t1' t2 : Tm} → t1 ⟨ τ r ⟩ t1' → (t1 · t2) ⟨ τ r ⟩ (t1' · t2)
 τ-app2 : ∀{t1 t2 t2' : Tm} → t2 ⟨ τ r ⟩ t2' → (t1 · t2) ⟨ τ r ⟩ (t1 · t2')
 τ-lam : ∀{x : V}{t t' : Tm} → t ⟨ τ r ⟩ t' → (ƛ x t) ⟨ τ r ⟩ (ƛ x t')


