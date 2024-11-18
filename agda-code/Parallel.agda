{- definition of parallel reduction relations, for proof of confluence.

   There is a generic definition of parallel reduction, which can be
   specialized for parallel α or parallel β.
-}
open import lib
open import relations
open import diamond
open import VarInterface

module Parallel(vi : VI) where

open VI vi
open import Ctxt vi
open import Tm vi
open import Subst vi
open import Beta vi
open import Alpha vi 
open import Tau vi 

{---------------------------------------------------------------------
 Parallel reduction

 We have

    t ⟨ ⇒c r ⟩ t'

 and
 
    t ⟨ ⇒ r ⟩ t'

 Both mean that t parallel reduces with r to t', but the former does 
 not allow an r step at the top level.  This is used to ensure that
 we cannot chain r steps together at the same position, so that ⇒ r is
 weaker than transitive closure of r.
----------------------------------------------------------------------}

mutual
 data ⇒ (r : ∀{Γ} → Rel (Tm Γ)) : ∀{Γ : Ctxt} → Tm Γ → Tm Γ → Set where
  ⇒ctxt : ∀{Γ : Ctxt}{t t' : Tm Γ} →
           t ⟨ ⇒c r ⟩ t' →
           t ⟨ ⇒ r ⟩ t'
  ⇒base : ∀{Γ : Ctxt}{t t' c : Tm Γ} → 
           t ⟨ ⇒c r ⟩ t' →
           t' ⟨ r ⟩ c → 
           t ⟨ ⇒ r ⟩ c
 data ⇒c (r : ∀{Γ} → Rel (Tm Γ)) : ∀{Γ : Ctxt} → Tm Γ → Tm Γ → Set where
  ⇒var : ∀{Γ : Ctxt}{x : V}
          {i : inCtxt x Γ} →
          var x i ⟨ ⇒c  r ⟩ var x i
  ⇒app : ∀{Γ : Ctxt}{t1 t1' t2 t2' : Tm Γ} → 
          t1 ⟨ ⇒ r ⟩ t1' →
          t2 ⟨ ⇒ r ⟩ t2' →
          (t1 · t2) ⟨ ⇒c r ⟩ (t1' · t2')
  ⇒lam : ∀{Γ : Ctxt}{x : V}{t1 t1' : Tm (x :: Γ)} →
           t1 ⟨ ⇒ r ⟩ t1' →
           (ƛ x t1) ⟨ ⇒c r ⟩ (ƛ x t1')

----------------------------------------------------------------------
-- Parallel alpha and beta
----------------------------------------------------------------------
⇒β : ∀{Γ : Ctxt} → Rel (Tm Γ)
⇒β = ⇒ β

⇒α : ∀{Γ : Ctxt} → Rel (Tm Γ)
⇒α = ⇒ α

----------------------------------------------------------------------
-- Some easy lemmas about parallel reduction in general
----------------------------------------------------------------------

-- parallel reduction is reflexive
mutual 
 ⇒refl : ∀{r : ∀{Γ} → Rel (Tm Γ)} → ∀{Γ} → reflexive (⇒ r {Γ})
 ⇒refl{_} {_} = ⇒ctxt ⇒crefl

 ⇒crefl : ∀{r : ∀{Γ} → Rel (Tm Γ)} → ∀{Γ} → reflexive (⇒c r {Γ})
 ⇒crefl{_} {_} {var x i} = ⇒var
 ⇒crefl{_} {_} {t1 · t2} = ⇒app ⇒refl ⇒refl
 ⇒crefl{_} {_} {ƛ x t} = ⇒lam ⇒refl

-- parallel reduction contains compatible reduction
τ⇒ : ∀{r : ∀{Γ} → Rel (Tm Γ)}{Γ : Ctxt} → (τ r {Γ}) ⊆ (⇒ r {Γ})
τ⇒ (τ-base x) = ⇒base ⇒crefl x
τ⇒ (τ-app1 x) = ⇒ctxt (⇒app (τ⇒ x) ⇒refl)
τ⇒ (τ-app2 x) = ⇒ctxt (⇒app ⇒refl (τ⇒ x))
τ⇒ (τ-lam x) = ⇒ctxt (⇒lam (τ⇒ x)) 

-- parallel reduction is contained in reflexive-transitive closure of compatible reduction
mutual 
 ⇒τ⋆ : ∀{r : ∀{Γ} → Rel (Tm Γ)}{Γ : Ctxt} → (⇒ r {Γ}) ⊆ ((τ r {Γ}) ⋆)
 ⇒τ⋆ (⇒ctxt d) = ⇒cτ⋆ d
 ⇒τ⋆ (⇒base d x) = ⇒cτ⋆ d ⋆trans (⋆base (τ-base x)) 

 ⇒cτ⋆ : ∀{r : ∀{Γ} → Rel (Tm Γ)}{Γ : Ctxt} → (⇒c r {Γ}) ⊆ ((τ r {Γ}) ⋆)
 ⇒cτ⋆ ⇒var = ⋆refl
 ⇒cτ⋆ (⇒app d1 d2) = (⋆app1 (⇒τ⋆ d1)) ⋆trans (⋆app2 (⇒τ⋆ d2))
 ⇒cτ⋆ (⇒lam d) = ⋆lam (⇒τ⋆ d)
