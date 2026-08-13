{- definition of parallel reduction, for proof of confluence.
-}
open import lib hiding (_>>=_ ; return )
open import relations
open import diamond
open import VarInterface

module Parallel where

open import Tm 
open import Subst
open import Apart
open import Renaming
open import Rename
open import AlphaCanon
open import Takahashi 

data ⇒αβ : Tm → Tm → Set where
  var : ∀{v : V} → 
          var v ⟨ ⇒αβ ⟩ var v
  app : ∀{t1 t2 t1' t2' : Tm} →
        t1 ⟨ ⇒αβ ⟩ t1' →
        t2 ⟨ ⇒αβ ⟩ t2' →
        t1 · t2 ⟨ ⇒αβ ⟩ t1' · t2'
  beta : ∀{t1 : Tm}{x : V}{t2 : Tm}{t1' t2' r : Tm} →
         t1 ⟨ ⇒αβ ⟩ t1' →
         t2 ⟨ ⇒αβ ⟩ t2' →        
         Subst t1' x t2' r → 
         (ƛ x t2) · t1 ⟨ ⇒αβ ⟩ r
  alpha : ∀{x x' : V}{t t' r : Tm} →
          x' ∈ t' ≡ ff →                              -- avoid capture
          x ≃ x' ≡ ff → 
          t ⟨ ⇒αβ ⟩ t' →
          Subst (var x') x t' r → 
          (ƛ x t) ⟨ ⇒αβ ⟩ (ƛ x' r)
  lam : ∀{t t' : Tm}{x : V} →
        t ⟨ ⇒αβ ⟩ t' →
        ƛ x t ⟨ ⇒αβ ⟩ ƛ x t'

⇒αβ-refl : ∀{t : Tm} → t ⟨ ⇒αβ ⟩ t
⇒αβ-refl {var x} = var
⇒αβ-refl {t · t₁} = app ⇒αβ-refl ⇒αβ-refl
⇒αβ-refl {ƛ x t} = lam ⇒αβ-refl

∉-⇒αβ : ∀{x : V}{s t : Tm} → 
         x ∈ s ≡ ff →
         s ⟨ ⇒αβ ⟩ t →
         x ∈ t ≡ ff
∉-⇒αβ {x} {s} {t} e var = e
∉-⇒αβ {x} {s1 · s2} {t} e (app x₁ x₂) with ||-≡-ff{x ∈ s1} e 
∉-⇒αβ {x} {s} {t} e (app x₁ x₂) | e1 , e2 rewrite ∉-⇒αβ e1 x₁ | ∉-⇒αβ e2 x₂ = refl
∉-⇒αβ {x} {(ƛ y s2) · s1} {t} e (beta x₁ x₂ x₃) with ||-≡-ff{~ x =ℕ y && x ∈ s2} e
∉-⇒αβ {x} {(ƛ y s2) · s1} {t} _ (beta x₁ x₂ x₃) | e1 , e2 with &&-ff-elim{~ x =ℕ y} e1
∉-⇒αβ {x} {(ƛ y s2) · s1} {t} _ (beta{t1' = t1'}{t2'} x₁ x₂ x₃) | e1 , e2 | inj₁ i rewrite =ℕ-to-≡{x}{y} (~ff-≡ i) = 
 var-∉-Subst {y} {t1'} {t2'} {t} (∉-⇒αβ e2 x₁) x₃
∉-⇒αβ {x} {(ƛ y s2) · s1} {t} _ (beta x₁ x₂ x₃) | e1 , e2 | inj₂ i = ∉-Subst (∉-⇒αβ e2 x₁) (∉-⇒αβ i x₂) x₃
∉-⇒αβ {x} {ƛ y s} {ƛ y' s'} e (alpha x₁ x₂ x₃ x₄) with &&-ff-elim{~ x =ℕ y} e
∉-⇒αβ {x} {ƛ y s} {ƛ y' s'} e (alpha{t' = t'} x₁ x₂ x₃ x₄) | inj₁ i rewrite =ℕ-to-≡{x}{y} (~ff-≡ i) | x₂ =
  var-∉-Subst{y}{var y'}{t'}{s'} x₂ x₄
∉-⇒αβ {x} {ƛ y s} {ƛ y' s'} e (alpha{t' = t'} x₁ x₂ x₃ x₄) | inj₂ i with keep (x ≃ y') 
∉-⇒αβ {x} {ƛ y s} {ƛ y' s'} e (alpha {t' = t'} x₁ x₂ x₃ x₄) | inj₂ i | tt , eq rewrite eq = refl
∉-⇒αβ {x} {ƛ y s} {ƛ y' s'} e (alpha {t' = t'} x₁ x₂ x₃ x₄) | inj₂ i | ff , eq rewrite eq = ∉-Subst{x}{y}{var y'}{t'}{s'} eq (∉-⇒αβ i x₃) x₄
∉-⇒αβ {x} {ƛ y s} {ƛ y t} e (lam x₁) with &&-ff-elim{~ x =ℕ y } e 
∉-⇒αβ {x} {ƛ y s} {ƛ y t} e (lam x₁) | inj₁ i rewrite i = refl
∉-⇒αβ {x} {ƛ y s} {ƛ y t} e (lam x₁) | inj₂ i rewrite ∉-⇒αβ i x₁ | &&-ff (~ x =ℕ y) = refl

{-
⇒αβ-subst : ∀{s1 s2 t1 t2 t : Tm}{y : V} → 
            Subst s1 y s2 t → 
            s1 ⟨ ⇒αβ ⟩ t1 → 
            s2 ⟨ ⇒αβ ⟩ t2 → 
            t ⟨ ⇒αβ ⟩ graft1 t1 y t2
⇒αβ-subst{t1}{t2}{t}{y} sb d1 d2  = {!!}
-}

varOk-tk : ∀{t : Tm}{vs : 𝕃 V} →
           varsub (fvs t) vs ≡ tt → 
           varOk vs t ≡ tt →
           t ⟨ ⇒αβ ⟩ (tk t)
varOk-tk{var x}{vs} sub ok = var
varOk-tk{var x · t}{vs} sub ok = app var (varOk-tk{t}{vs} (isSublist-++2l{eq = _≃_}{[ x ]}{fvs t}{vs} sub) (&&-elim2 ok))
varOk-tk{t1 · t2 · t3}{vs} sub ok =
 app (varOk-tk{t1 · t2}{vs} (isSublist-++1l{eq = _≃_}{fvs t1 ++ fvs t2}{fvs t3}{vs} sub) (&&-elim1 ok))
     (varOk-tk{t3}{vs} ((isSublist-++2l{eq = _≃_}{fvs t1 ++ fvs t2}{fvs t3}{vs} sub)) (&&-elim2 ok))
varOk-tk{(ƛ x t1) · t2}{vs} sub ok =
  beta {t2} {x} {t1} {tk t2} {tk t1}
    (varOk-tk {t2} {vs} (isSublist-++2l{eq = _≃_}{remove _≃_ x (fvs t1)}{fvs t2}{vs} sub)
       (&&-elim2 ok))
    (varOk-tk {t1} {x :: vs}
      (isSublist-remove{eq = _≃_}{fvs t1}{vs}{x} (λ{x} → ≃-sym{x})
        ((isSublist-++1l{eq = _≃_}{remove _≃_ x (fvs t1)}{fvs t2}{vs} sub)))
      (&&-elim2{~ varmem x vs} (&&-elim1 ok)))
    (substLem {!!})
varOk-tk{ƛ x t}{vs} sub ok =
 lam (varOk-tk {t} {x :: vs} (isSublist-remove{eq = _≃_}{fvs t}{vs}{x} (λ{x} → ≃-sym{x}) sub) (&&-elim2 ok))

triangle-⇒αβ : ∀{s t t' : Tm}{ρ : Renaming} →
                s ⟨ ⇒αβ ⟩ t →
                Rename ρ t t' → 
                t' ⟨ ⇒αβ ⟩ (αtk s ρ)
triangle-⇒αβ {var x} {t} {t'} {ρ} var var = var
triangle-⇒αβ {var x · s} {var x · t} {var y · t'} {ρ} (app var d) (app var re) = app var (triangle-⇒αβ{s}{t}{t'}{ρ} d re)
triangle-⇒αβ {s1 · s2 · s3} {t1 · t2} {t1' · t2'} {ρ} (app d1 d2) (app re1 re2) =
 app (triangle-⇒αβ{s1 · s2}{t1}{t1'}{ρ} d1 re1) (triangle-⇒αβ{s3}{t2}{t2'}{ρ} d2 re2)
triangle-⇒αβ {(ƛ x s1) · s2} {(ƛ x' t1) · t2} {t1' · t2'} {ρ} (app (alpha nf df d1 sb) d2) (app (lam ca re1) re2) =
 {!!}
triangle-⇒αβ {ƛ x s1 · s2} {ƛ x t1 · t2} {(ƛ x t1') · t2'} {ρ} (app (lam d1) d2) (app (lam ca re1) re2) = {!!}
triangle-⇒αβ {(ƛ x s1) · s2} {t} {t'} {ρ} (beta d1 d2 sb) re = {!!}
triangle-⇒αβ {ƛ y s} {ƛ z t} {ƛ z t'} {ρ} (alpha nf df d sb) (lam ca re) = {!!}
triangle-⇒αβ {ƛ y s} {ƛ y t} {ƛ y t'} {ρ} (lam d) (lam ca re) = {!!}

