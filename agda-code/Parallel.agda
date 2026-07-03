{- definition of parallel reduction, for proof of confluence.
-}
open import lib hiding (_>>=_ ; return)
open import relations
open import diamond
open import VarInterface

module Parallel where

open import Ctxt 
open import Tm 
open import Subst 
open import Takahashi 
open import Substitution 

data ⇒αβ : Tm → Tm → Set where
  refl-var : ∀{v : V} → var v ⟨ ⇒αβ ⟩ var v
  app : ∀{t1 t2 t1' t2' : Tm} →
        t1 ⟨ ⇒αβ ⟩ t1' →
        t2 ⟨ ⇒αβ ⟩ t2' →
        t1 · t2 ⟨ ⇒αβ ⟩ t1' · t2'
  beta : ∀{t1 t2 t1' t2' r : Tm}{x : V} →
        t1 ⟨ ⇒αβ ⟩ t1' →
        t2 ⟨ ⇒αβ ⟩ t2' →
        Subst [] t2' x t1' r → 
        (ƛ x t1) · t2 ⟨ ⇒αβ ⟩ r
  alpha : ∀{t1 t1' r : Tm}{x x' : V} →
        t1 ⟨ ⇒αβ ⟩ t1' →
        Subst [] (var x') x t1' r → 
        (ƛ x t1) ⟨ ⇒αβ ⟩ (ƛ x' r)
  lam : ∀{t1 t1' : Tm}{x : V} →
        t1 ⟨ ⇒αβ ⟩ t1' →
        ƛ x t1 ⟨ ⇒αβ ⟩ ƛ x t1'

⇒αβ-refl : ∀{t : Tm} → t ⟨ ⇒αβ ⟩ t
⇒αβ-refl{t} = {!!}


--trilem : 

subst-lem : ∀{g : Ctxt}{s2 : Tm}{v : V}{s1 : Tm}{vs : 𝕃 V}{σ : Substitution} →
            Subst g (αtk s2 vs σ) v (αtk s1 vs σ) (αtk-subst s2 v s1 vs σ)
subst-lem {g} {s2} {v} {var x}{vs}{σ} = {!!}
subst-lem {g} {s2} {v} {s1 · s3} = {!!}
subst-lem {g} {s2} {v} {ƛ x s1} = {!!}

triangle-⇒αβ : ∀{s t : Tm} →
               s ⟨ ⇒αβ ⟩ t →
               t ⟨ ⇒αβ ⟩ (αtk s [] [])
triangle-⇒αβ {s} {t} refl-var = ⇒αβ-refl
triangle-⇒αβ {var v · t2} {var v · t2'} (app refl-var x₁) = app ⇒αβ-refl (triangle-⇒αβ x₁) 
triangle-⇒αβ {s · s₂ · s₁} {t} (app x x₁) = app (triangle-⇒αβ x) (triangle-⇒αβ x₁)
triangle-⇒αβ {ƛ v s1 · s2} {t1 · t2} (app (alpha x x₁) x2) = {!!}
triangle-⇒αβ {ƛ v s1 · s2} {(ƛ v t1) · t2} (app (lam x1) x2) = beta (triangle-⇒αβ x1) (triangle-⇒αβ x2) {!!}
triangle-⇒αβ {(ƛ v s1) · s2} {t} (beta{t1' = t1}{t2} x x₁ x₂) = {!!}
triangle-⇒αβ {ƛ x s} {ƛ x' r} (alpha x₁ x₂) = {!!}
triangle-⇒αβ {ƛ x s} {ƛ x t} (lam x₁) = {!!}

{-

triangle-⇒αβ : ∀{vs : 𝕃 V}{σ : Substitution}{s t : Tm} →
               s ⟨ ⇒αβ ⟩ t →
               graft σ t ⟨ ⇒αβ ⟩ (αtk s vs σ)
triangle-⇒αβ {vs} {σ} {s} {t} refl-var = ⇒αβ-refl
triangle-⇒αβ {vs} {σ} {var v · t2} {var v · t2'} (app refl-var x₁) = app ⇒αβ-refl (triangle-⇒αβ x₁) 
triangle-⇒αβ {vs} {σ} {s · s₂ · s₁} {t} (app x x₁) = app (triangle-⇒αβ x) (triangle-⇒αβ x₁)
triangle-⇒αβ {vs} {σ} {ƛ v s1 · s2} {t1 · t2} (app (alpha x x₁) x2) = {!!}
triangle-⇒αβ {vs} {σ} {ƛ v s1 · s2} {(ƛ v t1) · t2} (app (lam x1) x2) = 
  beta (triangle-⇒αβ{vs} x1) (triangle-⇒αβ{vs} x2) {!!}
triangle-⇒αβ {vs} {σ} {(ƛ v s1) · s2} {t} (beta{t1' = t1}{t2} x x₁ x₂) = {!!}
triangle-⇒αβ {vs} {σ} {ƛ x s} {t} (alpha x₁ x₂) = {!!}
triangle-⇒αβ {vs} {σ} {ƛ x s} {t} (lam x₁) = {!!}
{-

triangle-⇒αβ {vs} {σ} {var v · t2} {var v · t2'} (app refl-var x₁) = app ⇒αβ-refl (triangle-⇒αβ{vs}{σ}{t2}{t2'} x₁) 
triangle-⇒αβ {vs} {σ} {t1 · t2 · t3} {t1' · t2' · t3'} (app x1 x2) =
  app (triangle-⇒αβ {vs} {σ} {t1 · t2} {t1' · t2'} x1) (triangle-⇒αβ x2)
triangle-⇒αβ {vs} {σ} {s} {t} (beta x x₁ x₂) = {!!}
triangle-⇒αβ {vs} {σ} {s} {t} (alpha x x₁) = {!!}
triangle-⇒αβ {vs} {σ} {s} {t} (lam x) = {!!}
-}-}