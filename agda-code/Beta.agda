open import lib
open import relations
open import VarInterface

module Beta(vi : VI) where

open VI vi
open import Tm vi
open import Ctxt vi
open import Subst vi
open import Tau vi
open import Alpha vi

β : ∀{Γ : Ctxt} → Rel (Tm Γ)
β ((ƛ x t1) · t2) = Subst t2 x t1
β _ _ = ⊥

↝β : ∀{Γ : Ctxt} → Rel (Tm Γ)
↝β = τ β

↝αβ : ∀{Γ : Ctxt} → Rel (Tm Γ)
↝αβ = ↝α ∪ ↝β

deterministic-β : ∀{Γ : Ctxt} → deterministic (β{Γ})
deterministic-β{Γ}{(ƛ x t1) · t2} d1 d2  = substDeterministic d1 d2