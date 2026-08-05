{- definition of parallel reduction, for proof of confluence.
-}
open import lib hiding (_>>=_ ; return )
open import relations
open import diamond
open import VarInterface

module Parallel where

open import Tm 
open import Subst
open import Substitution
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

triangle-⇒αβ : ∀{s t : Tm} →
                varOk s ≡ tt → 
                s ⟨ ⇒αβ ⟩ t →
                t ⟨ ⇒αβ ⟩ (tk s)
triangle-⇒αβ {var x} {t} vok var = var
triangle-⇒αβ {var x · s2} {t1 · t2} vok (app var d2) = app var (triangle-⇒αβ vok d2)
triangle-⇒αβ {s1 · s2 · s3} {t1 · t2} vok (app d1 d2) =
  app (triangle-⇒αβ {s1 · s2} {t1} (&&-elim1 vok) d1) (triangle-⇒αβ {s3} {t2} (&&-elim2 vok) d2)
triangle-⇒αβ {ƛ x s1 · s2} {t1 · t2} vok (app (alpha v n d u) d2) = {!!}
triangle-⇒αβ {ƛ x s1 · s2} {t1 · t2} vok (app (lam d1) d2) = {!!}
triangle-⇒αβ {(ƛ y s1) · s2} {t} vok (beta d1 d2 u) = {!!}
triangle-⇒αβ {ƛ y s} {ƛ y' t} vok (alpha v n d u) = {!!}
triangle-⇒αβ {ƛ y s} {ƛ y t } vok (lam d) = {!!}