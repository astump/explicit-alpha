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

subst-αtk :
  ∀{t1 t2 t1' t2' s1 s2 t : Tm}{x : V}{vs : 𝕃 V}{σ : Substitution} → 
  t1 ⟨ ⇒αβ ⟩ t1' →
  t2 ⟨ ⇒αβ ⟩ t2' →   
  t1' ≡ αtk s1 vs σ →
  t2' ≡ αtk s2 vs σ →  
  Subst t1 x t2 t →
  t ⟨ ⇒αβ ⟩ αtk-subst s1 x s2 vs σ
subst-αtk {t1} {var x} {.(αtk s1 vs σ)} {var x} {s1} {s2} {t1} {x} {vs} {σ} d1 var refl eq2 var-found rewrite eq2
{-  with αtk-∘{s2}{vs}{[ x , αtk s1 vs [] ]}{[]} {!!} {!!} 
subst-αtk {t1} {var x} {.(αtk s1 vs [])} {var x} {s1} {s2} {t1} {x} {vs} d1 var refl eq2 var-found | p  -}
   = {!!}
subst-αtk {t1} {var v} {t1'} {var v} {s1} {s2} {var v} {x} {vs} {σ} d1 var eq1 eq2 (var-not x₁) rewrite eq2 = {!!}
subst-αtk {t1} {t2} {t1'} {t2'} {s1} {s2} {t} {x} {vs} {σ} d1 d2 eq1 eq2 (app su su₁) = {!!}
subst-αtk {t1} {t2} {t1'} {t2'} {s1} {s2} {t} {x} {vs} {σ} d1 d2 eq1 eq2 (lam-go x₁ x₂ su) = {!!}
subst-αtk {t1} {t2} {t1'} {t2'} {s1} {s2} {t} {x} {vs} {σ} d1 d2 eq1 eq2 (lam-stop x₁) = {!!}

triangle-⇒αβ : ∀{s t : Tm}{vs : 𝕃 V} →
               s ⟨ ⇒αβ ⟩ t →
               t ⟨ ⇒αβ ⟩ (αtk s vs [])
triangle-⇒αβ {s} {t}{vs} var = var
triangle-⇒αβ {s} {t}{vs} (app x1 x2) = {!!}
triangle-⇒αβ {(ƛ x s2) · s1} {t}{vs} (beta x1 x2 u) =
  let p1 = triangle-⇒αβ{vs = vs} x1 in
  let p2 = triangle-⇒αβ{vs = vs} x2 in
    {!!}
triangle-⇒αβ {s} {t}{vs} (alpha fr ne x2 u) = {!!}
triangle-⇒αβ {s} {t}{vs} (lam x) = {!!}