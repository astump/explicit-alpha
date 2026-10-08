{- definition of parallel reduction
-}
open import lib
open import relations
open import VarInterface

module Parallel(vi : VI) where

open VI vi

open import Tm vi
open import Subst vi

{- parallel reduction, including both alpha- and beta-steps.

   The boolean tells whether or not this is alpha-free -}
data ⇒αβ : 𝔹 → Tm → Tm → Set where
  var : ∀{v : V}{b : 𝔹} → 
          var v ⟨ ⇒αβ b ⟩ var v
  app : ∀{t1 t2 t1' t2' : Tm}{b1 b2 : 𝔹} →
        (d1 : t1 ⟨ ⇒αβ b1 ⟩ t1') →
        (d2 : t2 ⟨ ⇒αβ b2 ⟩ t2') →
        t1 · t2 ⟨ ⇒αβ (b1 && b2) ⟩ t1' · t2'
  beta : ∀{t1 : Tm}{x : V}{t2 : Tm}{t1' t2' r : Tm}{b1 b2 : 𝔹} →
         (d1 : t1 ⟨ ⇒αβ b1 ⟩ t1') →
         (d2 : t2 ⟨ ⇒αβ b2 ⟩ t2') →        
         (sb : Subst t1' x t2' r) → 
         (ƛ x t2) · t1 ⟨ ⇒αβ (b1 && b2) ⟩ r
  alpha : ∀{x x' : V}{t t' r : Tm}{b : 𝔹} →
          (nf : x' ∈ t' ≡ ff) →                              -- avoid capture
          (ne : x ≃ x' ≡ ff) → 
          (d : t ⟨ ⇒αβ b ⟩ t') →
          (sb : Subst (var x') x t' r) → 
          (ƛ x t) ⟨ ⇒αβ ff ⟩ (ƛ x' r)
  lam : ∀{t t' : Tm}{x : V}{b : 𝔹} →
        (d : t ⟨ ⇒αβ b ⟩ t') →
        ƛ x t ⟨ ⇒αβ b ⟩ ƛ x t'

