open import lib
open import VarInterface

module Subst(vi : VI) where

open VI vi

open import Tm vi
open import Substitution vi
open import Apart vi
open import VarOps vi

data Subst : Tm → V → Tm → Tm → Set where
  var-found : ∀{t : Tm}{v : V} → 
              Subst t v (var v) t
  var-not : ∀{t : Tm}{v x : V} →
             v ≃ x ≡ ff → 
             Subst t v (var x) (var x)
  app : ∀{t : Tm}{v : V}
         {t1 t2 t1' t2' : Tm} → 
         Subst t v t1 t1' →
         Subst t v t2 t2' →
         Subst t v (t1 · t2) (t1' · t2')
  lam-go : ∀{t : Tm}{v : V}{x : V}{s s' : Tm} →
           v ∈ (ƛ x s) ≡ tt →
           x ∈ t ≡ ff →                 -- avoid capture
           Subst t v s s' →
           Subst t v (ƛ x s) (ƛ x s')
  lam-stop : ∀{t : Tm}{v : V}{x : V}{s : Tm} →
             v ∈ (ƛ x s) ≡ ff →
             Subst t v (ƛ x s) (ƛ x s)

