open import lib hiding (_>>=_ ; return ; _∘_)
open import bool-relations
open import VarInterface

module Lemmas.VarInterface(vi : VI) where

open VI vi

open import Fresh


≃-refl = fst (fst ≃-equivalence)
≃-sym = snd ≃-equivalence
≃-trans = snd (fst ≃-equivalence)
~≃-sym = ~symmetric _≃_ ≃-sym
~≃-sym2 = ~symmetric2 _≃_ ≃-sym

¬≃ : ∀{x y : V} → ¬ (x ≃ y ≡ tt) → x ≃ y ≡ ff 
¬≃{x}{y} p with x ≃ y 
¬≃{x}{y} p | tt with (p refl)
¬≃{x}{y} p | tt | ()
¬≃{x}{y} p | ff = refl


≃-⊥ : ∀{x : V} → (x ≃ x) ≡ ff → ∀{X : Set} → X
≃-⊥{x} u rewrite ≃-refl{x} with u
≃-⊥{x} u | ()

≃-uip : ∀{x y : V}{b : 𝔹}(p q : x ≃ y ≡ b) → p ≡ q
≃-uip{x}{y} p q with x ≃ y 
≃-uip{x}{y} refl refl | u = refl
