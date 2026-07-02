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
open import Alpha 
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

αtkP : TkM Tm → Set
αtkP x = ∀{vs : 𝕃 V}{σ : Substitution} →
          ∃ Tm (λ s → x ≡ αtk s ∧ 
          ∀{t : Tm} →
          s ⟨ ⇒αβ ⟩ t →
          graft σ t ⟨ ⇒αβ ⟩ fst (x vs σ))

αtk-case : ∀{x : TkM Tm}{f : Tm → TkM Tm} →
          αtkP x →
          (∀{r : Tm} → αtkP (f r)) → 
          αtkP (x >>=tk f)
αtk-case{x} px pf {vs}{σ} with px{vs}{σ} 
αtk-case{x} px pf {vs}{σ} | s , eq , ux with x vs σ
αtk-case{x} px pf {vs}{σ} | s , eq , ux | (s' , vs' , σ') with pf{s'}{vs'}{σ'} 
αtk-case{x} px pf {vs}{σ} | s , eq , ux | (s' , vs' , σ') | (s'' , eq' , uf) = {!!} , {!!}

--trilem : 

triangle-⇒αβ : ∀{vs : 𝕃 V}{σ : Substitution}{s t : Tm} →
               s ⟨ ⇒αβ ⟩ t →
               graft σ t ⟨ ⇒αβ ⟩ fst (αtk s vs σ)
triangle-⇒αβ {vs} {σ} {s} {t} refl-var = ⇒αβ-refl
triangle-⇒αβ {vs} {σ} {var v · t2} {var v · t2'} (app refl-var x₁) = app ⇒αβ-refl (triangle-⇒αβ{vs}{σ}{t2}{t2'} x₁) 
triangle-⇒αβ {vs} {σ} {t1 · t2 · t3} {t1' · t2' · t3'} (app (app x1 x2) x3) =
  app (triangle-⇒αβ {vs} {σ} {t1 · t2} {t1' · t2'} (app x1 x2)) {!triangle-⇒αβ x3!}
triangle-⇒αβ {vs} {σ} {s} {t} (app (beta x x₂ x₃) x₁) = {!!}
triangle-⇒αβ {vs} {σ} {s} {t} (app (alpha x x₂) x₁) = {!!}
triangle-⇒αβ {vs} {σ} {s} {t} (app (lam x) x₁) = {!!}
triangle-⇒αβ {vs} {σ} {s} {t} (beta x x₁ x₂) = {!!}
triangle-⇒αβ {vs} {σ} {s} {t} (alpha x x₁) = {!!}
triangle-⇒αβ {vs} {σ} {s} {t} (lam x) = {!!}
