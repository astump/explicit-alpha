{- definition of parallel reduction, for proof of confluence.
-}
open import lib hiding (_>>=_ ; return )
open import relations
open import diamond
open import VarInterface

module Parallel where

open import Apart
open import Ctxt 
open import Tm 
open import Subst 
open import Takahashi 
open import Substitution 

infix 6 _⇒αβ_

data _⇒αβ_ : Ctxt → Substitution → Tm → Tm → Set where
  var-found : ∀{v : V}{Γ : Ctxt}{σ : Substitution}{t : Tm} → 
              lookup σ v ≡ just t → 
              Apart t Γ → 
              var v ⟨ Γ ⇒αβ σ ⟩ t
  var-not : ∀{v : V}{Γ : Ctxt}{σ : Substitution} → 
              lookup σ v ≡ nothing → 
              var v ⟨ Γ ⇒αβ σ ⟩ var v
  app : ∀{t1 t2 t1' t2' : Tm}{σ : Substitution}{Γ : Ctxt} →
        t1 ⟨ Γ ⇒αβ σ ⟩ t1' →
        t2 ⟨ Γ ⇒αβ σ ⟩ t2' →
        t1 · t2 ⟨ Γ ⇒αβ σ ⟩ t1' · t2'
  beta : ∀{t1 : Tm}{x : V}{t2 : Tm}{t1' r : Tm}{σ : Substitution}{Γ : Ctxt} →
        t1 ⟨ Γ ⇒αβ σ ⟩ t1' →
        t2 ⟨ Γ ⇒αβ ([ t1' / x ] σ) ⟩ r →
        (ƛ x t2) · t1 ⟨ Γ ⇒αβ σ ⟩ r
  alpha : ∀{t t' : Tm}{x x' : V}{σ : Substitution}{Γ : Ctxt} →
        t ⟨ Γ ⇒αβ ([ var x' / x ] σ) ⟩ t' →
        x' ∉ t →                              -- avoid capture
        (ƛ x t) ⟨ Γ ⇒αβ σ ⟩ (ƛ x' t')
  lam : ∀{t t' : Tm}{x : V}{σ : Substitution}{Γ : Ctxt} →
        t ⟨ (x :: Γ) ⇒αβ σ ⟩ t' →
        ƛ x t ⟨ Γ ⇒αβ σ ⟩ ƛ x t'

⇒αβ-subst-var : ∀{Γ : Ctxt}{σ : Substitution}{x : V} →
                Apart (subst-var σ x) Γ →
                var x ⟨ Γ ⇒αβ σ ⟩ subst-var σ x
⇒αβ-subst-var{Γ}{σ}{x} apart with keep (lookup σ x) 
⇒αβ-subst-var {Γ} {σ} {x} apart | nothing , p rewrite lookup-nothing{σ} p = var-not p
⇒αβ-subst-var {Γ} {σ} {x} apart | just t , p rewrite lookup-just{σ} p = var-found p apart

⇒αβ-refl : ∀{Γ : Ctxt}{σ : Substitution}{t r : Tm} →
           Subst Γ σ t r → 
           t ⟨ Γ ⇒αβ σ ⟩ r
⇒αβ-refl {Γ} {σ} {var x} {r} (var-found u v) = var-found u v
⇒αβ-refl {Γ} {σ} {var x} {var x} (var-not u) = var-not u
⇒αβ-refl {Γ} {σ} {t} {r} (app s1 s2) = app (⇒αβ-refl s1) (⇒αβ-refl s2)
⇒αβ-refl {Γ} {σ} {t} {r} (lam s) = lam (⇒αβ-refl s)

data ⇒Args(Γ : Ctxt) : Substitution → Substitution → Substitution → Set where
  arg-nil : ∀{σ : Substitution} → ⇒Args Γ [] [] σ
  arg-cons : ∀{x : V}{s t : Tm}{σ1 σ2 σ : Substitution} →
              s ⟨ Γ ⇒αβ (σ2 ++ σ) ⟩ t → 
              ⇒Args Γ σ1 σ2 σ →
              ⇒Args Γ ([ s / x ] σ1) ([ t / x ] σ2) σ



triangle-⇒αβ : ∀{Γ : Ctxt}{σ1 σ2 σ : Substitution} →
               (a : ⇒Args Γ σ1 σ2 σ) →
               ∀{s t : Tm} →
               s ⟨ Γ ⇒αβ (σ2 ++ σ) ⟩ t →
               t ⟨ Γ ⇒αβ [] ⟩ (αtk (redexes σ1 s) Γ σ)
triangle-⇒αβ {Γ} {σ1} {σ2} {σ} a {s} {t} (var-found x x₁) = {!!}
triangle-⇒αβ {Γ} {σ1} {σ2} {σ} a {s} {t} (var-not x) = {!!}
triangle-⇒αβ {Γ} {σ1} {σ2} {σ} a {s} {t} (app x x₁) = {!!}
triangle-⇒αβ {Γ} {σ1} {σ2} {σ} a {(ƛ v s2) · s1} {t} (beta{t1' = t1} x x₁) =
  let p = triangle-⇒αβ (arg-cons{Γ}{v} x a) x₁ in
    {!!}
triangle-⇒αβ {Γ} {σ1} {σ2} {σ} a {s} {t} (alpha x x₁) = {!!}
triangle-⇒αβ {Γ} {σ1} {σ2} {σ} a {s} {t} (lam x) = {!!}
{-
triangle-⇒αβ arg-nil (var-found x _) rewrite x = ⇒αβ-refl Subst-refl
triangle-⇒αβ arg-nil (var-not x) rewrite x = ⇒αβ-refl Subst-refl 
triangle-⇒αβ arg-nil {var v · s2} {t1 · t2} (app x1 x2) = app (triangle-⇒αβ arg-nil x1) (triangle-⇒αβ arg-nil x2)
triangle-⇒αβ arg-nil {s1 · s2 · s3} {t1 · t2} (app x1 x2) = app (triangle-⇒αβ arg-nil x1) (triangle-⇒αβ arg-nil x2)
triangle-⇒αβ arg-nil {(ƛ v s1) · s2} {t1 · t2} (app x1 x2) = {!!}
--triangle-⇒αβ{Γ}{σ} arg-nil (beta{s1}{v}{s2}{t1}{r} x1 x2) = {!!} --triangle-⇒αβ (arg-cons{x = v} x1 (arg-nil{Γ}{[ t1 / v ] σ})) x2 
triangle-⇒αβ{Γ}{σ} a (beta{s1}{v}{s2}{t1}{r} x1 x2) = triangle-⇒αβ (arg-cons{x = v} x1 {!!}) {!!}

triangle-⇒αβ arg-nil (alpha x1 x2) = {!!}
triangle-⇒αβ arg-nil (lam x) = {!!}

triangle-⇒αβ (arg-cons x a) d = {!!}
-}
{-
mutual 
 triangle-⇒αβ : ∀{s t : Tm}{Γ : Ctxt}{σ : Substitution} →
                s ⟨ Γ ⇒αβ σ ⟩ t →
                t ⟨ Γ ⇒αβ [] ⟩ (αtk s Γ σ)

 subst-⇒αβ : ∀{Γ : Ctxt}{σ : Substitution}{s1 s2 t1 t2 : Tm}{x : V} →
             s1 ⟨ Γ ⇒αβ σ ⟩ t1 → 
             s2 ⟨ Γ ⇒αβ ([ t1 / x ] σ) ⟩ t2 → 
             t2 ⟨ Γ ⇒αβ [] ⟩ αtk-subst s1 x s2 Γ σ
 subst-⇒αβ{x = v} d1 (var-found{v'} x1 x2) with keep (v' ≃ v) 
 subst-⇒αβ {x = v} d1 (var-found {v'} x1 x2) | tt , p rewrite p with x1 
 subst-⇒αβ {x = v} d1 (var-found {v'} x1 x2) | tt , p | refl = triangle-⇒αβ d1
 subst-⇒αβ {x = v} d1 (var-found {v'} x1 x2) | ff , p rewrite p | x1 = ⇒αβ-refl Subst-refl
 subst-⇒αβ {x = v} d1 (var-not{v'} x) with keep (v' ≃ v) 
 subst-⇒αβ {x = v} d1 (var-not {_} x) | tt , p rewrite p with x
 subst-⇒αβ {x = v} d1 (var-not {_} x) | tt , p | ()
 subst-⇒αβ {x = v} d1 (var-not {_} x) | ff , p rewrite p | x = ⇒αβ-refl Subst-refl
 subst-⇒αβ d1 (app x1 x2) = {!!}
 subst-⇒αβ d1 (beta x1 x2) = {!!}
 subst-⇒αβ d1 (alpha x1 x2) = {!!}
 subst-⇒αβ d1 (lam x) = {!!}


{-
triangle-⇒αβ : ∀{s t t' : Tm}{Γ : Ctxt}{σ : Substitution} →
               Subst Γ σ t t' → 
               s ⟨ Γ ⇒αβ σ ⟩ t' →
               t ⟨ Γ ⇒αβ σ ⟩ (αtk s Γ σ)
triangle-⇒αβ {s} {t} {t'} {Γ} {σ} u (var-found{v = v} x1 x2) rewrite lookup-just{σ}{v}{t'} x1 = ⇒αβ-refl u
triangle-⇒αβ {s} {t} {t'} {Γ} {σ} u (var-not{v = v} x) rewrite lookup-nothing{σ}{v} x = ⇒αβ-refl u
triangle-⇒αβ {s1 · s2} {t} {var x · t2'} {Γ} {σ} u (app x1 x2) = {!!}
triangle-⇒αβ {s1 · s2} {t} {t1' · t1'' · t2'} {Γ} {σ} u (app x1 x2) = {!!}
triangle-⇒αβ {s1 · s2} {t} {ƛ x t1' · t2'} {Γ} {σ} u (app x1 x2) = {!!}
triangle-⇒αβ {(ƛ x t1) · t2} {t} {t'} {Γ} {σ} u (beta x1 x2) = {!!}
triangle-⇒αβ {s} {t} {t'} {Γ} {σ} u (alpha x1 x2) = {!!}
triangle-⇒αβ {s} {t} {t'} {Γ} {σ} u (lam x) = {!!}
-}
{-
triangle-⇒αβ : ∀{s t : Tm}{σ : Substitution} →
               s ⟨ ⇒αβ σ ⟩ t →
               t ⟨ ⇒αβ σ ⟩ (αtk s [] σ)
triangle-⇒αβ {s} {t} refl-var = ?
triangle-⇒αβ {var v · t2} {var v · t2'} (app refl-var x₁) = app ⇒αβ-refl (triangle-⇒αβ x₁) 
triangle-⇒αβ {s · s₂ · s₁} {t} (app x x₁) = app (triangle-⇒αβ x) (triangle-⇒αβ x₁)
triangle-⇒αβ {ƛ v s1 · s2} {t1 · t2} (app (alpha x x₁) x2) = {!!}
triangle-⇒αβ {ƛ v s1 · s2} {(ƛ v t1) · t2} (app (lam x1) x2) = beta (triangle-⇒αβ x1) (triangle-⇒αβ x2) {!!}
triangle-⇒αβ {(ƛ v s1) · s2} {t} (beta{t1' = t1}{t2} x x₁ x₂) = {!!}
triangle-⇒αβ {ƛ x s} {ƛ x' r} (alpha x₁ x₂) = {!!}
triangle-⇒αβ {ƛ x s} {ƛ x t} (lam x₁) = {!!}

-}-}