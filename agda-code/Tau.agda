open import lib
open import relations 
open import VarInterface

module Tau(vi : VI) where

open VI vi
open import Ctxt vi
open import Tm vi

data τ(r : ∀{Γ} → Rel (Tm Γ)) : ∀{Γ : Ctxt} → Rel (Tm Γ) where
 τ-base : ∀ {Γ : Ctxt}{t1 t2 : Tm Γ} → t1 ⟨ r ⟩ t2 → t1 ⟨ τ r ⟩ t2
 τ-app1 : ∀ {Γ : Ctxt}{t1 t1' t2 : Tm Γ} → t1 ⟨ τ r ⟩ t1' → (t1 · t2) ⟨ τ r ⟩ (t1' · t2)
 τ-app2 : ∀ {Γ : Ctxt}{t1 t2 t2' : Tm Γ} → t2 ⟨ τ r ⟩ t2' → (t1 · t2) ⟨ τ r ⟩ (t1 · t2')
 τ-lam : ∀{Γ : Ctxt}{x : V}{t t' : Tm (x :: Γ)} → t ⟨ τ r ⟩ t' → (ƛ x t) ⟨ τ r ⟩ (ƛ x t')

τ-symm : ∀{r : {Γ : Ctxt} → Rel (Tm Γ)} → (∀{Γ : Ctxt} → symmetric (r{Γ})) → ∀{Γ : Ctxt} → symmetric (τ r {Γ})
τ-symm u (τ-base x) = τ-base (u x)
τ-symm u (τ-app1 p) = τ-app1 (τ-symm u p)
τ-symm u (τ-app2 p) = τ-app2 (τ-symm u p)
τ-symm u (τ-lam p) = τ-lam (τ-symm u p)

⋆app1 : ∀{Γ : Ctxt}{t1 t1' t2 : Tm Γ}{r : {Γ : Ctxt} → Rel (Tm Γ)} →
         t1 ⟨ (τ r) ⋆ ⟩ t1' →
         (t1 · t2) ⟨ (τ r) ⋆ ⟩ (t1' · t2)
⋆app1 ⋆refl = ⋆refl
⋆app1 (⋆base p) = ⋆base (τ-app1 p)
⋆app1 (p1 ⋆trans p2) = (⋆app1 p1) ⋆trans (⋆app1 p2)

⋆app2 : {Γ : Ctxt}{t1 t2 t2' : Tm Γ}{r : {Γ : Ctxt} → Rel (Tm Γ)} →
         t2 ⟨ (τ r) ⋆ ⟩ t2' →
         (t1 · t2) ⟨ (τ r) ⋆ ⟩ (t1 · t2')
⋆app2 ⋆refl = ⋆refl
⋆app2 (⋆base p) = ⋆base (τ-app2 p)
⋆app2 (p1 ⋆trans p2) = (⋆app2 p1) ⋆trans (⋆app2 p2)

⋆lam : ∀{Γ : Ctxt}{x : V}{t t' : Tm (x :: Γ)}{r : {Γ : Ctxt} → Rel (Tm Γ)} →
         t ⟨ (τ r) ⋆ ⟩ t' →
         (ƛ x t) ⟨ (τ r) ⋆ ⟩ (ƛ x t')
⋆lam ⋆refl = ⋆refl
⋆lam (⋆base p) = ⋆base (τ-lam p)
⋆lam (p1 ⋆trans p2) = (⋆lam p1) ⋆trans (⋆lam p2)
