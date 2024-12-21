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
--open import Alpha vi 
open import Tau vi 
open import Apart vi

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
 data ⇒ (r : Rel Tm) : Tm → Tm → Set where
  ⇒ctxt : ∀{t t' : Tm} →
           t ⟨ ⇒c r ⟩ t' →
           t ⟨ ⇒ r ⟩ t'
  ⇒base : ∀{t t' c : Tm} → 
           t ⟨ ⇒c r ⟩ t' →
           t' ⟨ r ⟩ c → 
           t ⟨ ⇒ r ⟩ c
 data ⇒c (r : Rel Tm) : Tm → Tm → Set where
  ⇒var : ∀{x : V} → 
          var x ⟨ ⇒c r ⟩ var x
  ⇒app : ∀{t1 t1' t2 t2' : Tm} → 
          t1 ⟨ ⇒ r ⟩ t1' →
          t2 ⟨ ⇒ r ⟩ t2' →
          (t1 · t2) ⟨ ⇒c r ⟩ (t1' · t2')
  ⇒lam : ∀{x : V}{t1 t1' : Tm} →
           t1 ⟨ ⇒ r ⟩ t1' →
           (ƛ x t1) ⟨ ⇒c r ⟩ (ƛ x t1')

----------------------------------------------------------------------
-- Parallel alpha and beta
----------------------------------------------------------------------
⇒β : Rel Tm
⇒β = ⇒ β

{-
⇒α : Rel Tm
⇒α = ⇒ α
-}

----------------------------------------------------------------------
-- Some easy lemmas about parallel reduction in general
----------------------------------------------------------------------

-- parallel reduction is reflexive
mutual 
 ⇒refl : ∀{r : Rel Tm} → reflexive (⇒ r )
 ⇒refl{_} {_} = ⇒ctxt ⇒crefl

 ⇒crefl : ∀{r : Rel Tm} → reflexive (⇒c r)
 ⇒crefl {_} {var x} = ⇒var
 ⇒crefl {_} {t1 · t2} = ⇒app ⇒refl ⇒refl
 ⇒crefl {_} {ƛ x t} = ⇒lam ⇒refl


-- parallel reduction contains compatible reduction
τ⇒ : ∀{r : Rel Tm} → (τ r) ⊆ (⇒ r)
τ⇒ (τ-base x) = ⇒base ⇒crefl x
τ⇒ (τ-app1 x) = ⇒ctxt (⇒app (τ⇒ x) ⇒refl)
τ⇒ (τ-app2 x) = ⇒ctxt (⇒app ⇒refl (τ⇒ x))
τ⇒ (τ-lam x) = ⇒ctxt (⇒lam (τ⇒ x)) 

-- parallel reduction is contained in reflexive-transitive closure of compatible reduction
mutual 
 ⇒τ⋆ : ∀{r : Rel Tm} → (⇒ r) ⊆ ((τ r) ⋆)
 ⇒τ⋆ (⇒ctxt d) = ⇒cτ⋆ d
 ⇒τ⋆ (⇒base d x) = ⇒cτ⋆ d ⋆trans (⋆base (τ-base x)) 

 ⇒cτ⋆ : ∀{r : Rel Tm} → (⇒c r) ⊆ ((τ r) ⋆)
 ⇒cτ⋆ ⇒var = ⋆refl
 ⇒cτ⋆ (⇒app d1 d2) = (⋆app1 (⇒τ⋆ d1)) ⋆trans (⋆app2 (⇒τ⋆ d2))
 ⇒cτ⋆ (⇒lam d) = ⋆lam (⇒τ⋆ d)

-- parallel reduction preserves apartness if r does
preserves-Apart : Rel Tm → Set
preserves-Apart r = ∀{Γ : Ctxt}{t t' : Tm} →
                     Apart t Γ →
                     t ⟨ r ⟩ t' →
                     Apart t' Γ

mutual 
 Apart-⇒ : ∀{r : Rel Tm} →
            preserves-Apart r →
            preserves-Apart (⇒ r)
 Apart-⇒ pr a (⇒ctxt x) = Apart-⇒c pr a x
 Apart-⇒ pr a (⇒base x x₁) = pr (Apart-⇒c pr a x) x₁

 Apart-⇒c : ∀{r : Rel Tm} →
             preserves-Apart r →
             preserves-Apart (⇒c r)
 Apart-⇒c pr A ⇒var = A
 Apart-⇒c pr A (⇒app x x₁) = Apart· (Apart-⇒ pr (Apart1 A) x) (Apart-⇒ pr (Apart2 A) x₁)
 Apart-⇒c pr A (⇒lam x) = Apartƛ (Apart-⇒ pr (Apartƛ1 A) x) (Apartƛ2 A)

Apart-Subst : ∀{Γ Γ' : Ctxt}{t t' r : Tm}{x : V} →
               Apart t Γ →
               Apart t' Γ →               
               Subst Γ' t' x t r →
               Apart r Γ
Apart-Subst{Γ}{r} A1 A2 (substVarFound A') = A2
Apart-Subst{Γ}{r} A1 A2 (substVarNot u) = A1
Apart-Subst{Γ}{r} A1 A2 (substApp s1 s2) = Apart· (Apart-Subst (Apart1 A1) A2 s1) (Apart-Subst (Apart2 A1) A2 s2)
Apart-Subst{Γ}{r} A1 A2 (substLam s) = Apartƛ (Apart-Subst A2 A2 s) (Apartƛ2 A1)

Apart-β : preserves-Apart β
Apart-β{Γ}{(ƛ x t) · t'} A s = Apart-Subst (Apartƛ1 (Apart1 A)) (Apart2 A) s

Apart-⇒β : preserves-Apart (⇒ β)
Apart-⇒β = Apart-⇒ Apart-β

Apart-⇒cβ : preserves-Apart (⇒c β)
Apart-⇒cβ = Apart-⇒c Apart-β