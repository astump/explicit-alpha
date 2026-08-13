open import lib
open import VarInterface

module Rename where

open import Tm 
open import Renaming

data Rename : Renaming → Tm → Tm → Set where
  var : ∀{v : V}{ρ : Renaming} → 
         Rename ρ (var v) (var (rename ρ v))
  app : ∀{t1 t2 t1' t2' : Tm}{ρ : Renaming} → 
         Rename ρ t1 t1' →
         Rename ρ t2 t2' →
         Rename ρ (t1 · t2) (t1' · t2')
  lam : ∀{x : V}{s s' : Tm}{ρ : Renaming} →
        varmem x (ranr ρ) ≡ ff →                 -- avoid capture
        Rename (ρ \\ x) s s' →
        Rename ρ (ƛ x s) (ƛ x s')

