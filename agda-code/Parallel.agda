{- definition of parallel reduction, for proof of confluence.
-}
open import lib hiding (_>>=_ ; return )
open import relations
open import diamond
open import VarInterface

module Parallel where

open import Tm 
open import Subst 
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
          x' ∈ t ≡ ff →                              -- avoid capture
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

subst-⇒αβ :
  ∀{t1 t2 r1 r2 t : Tm}{x : V} → 
  t1 ⟨ ⇒αβ ⟩ r1 → 
  t2 ⟨ ⇒αβ ⟩ r2 → 
  Subst t1 x t2 t →
  Apart r1 (bvs r2) ≡ tt →  -- cannot capture a variable of r1 substituting into r2
  ∃ Tm (λ q → Subst r1 x r2 q ∧ t ⟨ ⇒αβ ⟩ q)
subst-⇒αβ{r1 = r1} d1 var var-found apart = r1 , var-found , d1
subst-⇒αβ d1 var (var-not{v = v}{x = v'} x) apart = var v' , var-not x , var
subst-⇒αβ{t1}{ta · tb}{r1} d1 (app{t1' = ta'}{t2' = tb'} da db) (app ua ub) apart with (list-all-append (λ v → ~ v ∈ r1) (bvs ta') (bvs tb'))
subst-⇒αβ{t1}{ta · tb}{r1} d1 (app{t1' = ta'}{t2' = tb'} da db) (app ua ub) apart | p rewrite p with &&-elim{Apart r1 (bvs ta')} apart
subst-⇒αβ{t1}{ta · tb}{r1} d1 (app{t1' = ta'}{t2' = tb'} da db) (app ua ub) apart | p | p1 , p2
  with subst-⇒αβ d1 da ua p1 | subst-⇒αβ d1 db ub p2
subst-⇒αβ{t1}{ta · tb}{r1} d1 (app{t1' = ta'}{t2' = tb'} da db) (app{t1' = r1'}{t2' = r2'} u1 u2) apart | p | p1 , p2
  | q1 , sq1 , dq1 | q2 , sq2 , dq2  = q1 · q2 , app sq1 sq2 , app dq1 dq2
subst-⇒αβ d1 (beta x x₁ x₂) (app s1 s2) = {!!}
subst-⇒αβ{t1}{ƛ y t2}{r1}{r2}{ƛ y r}{z} d1 d2 (lam-go x x₁ s) apart with &&-elim{~ z =ℕ y} x 
subst-⇒αβ {t1} {ƛ y t2} {r1} {ƛ y' r'} {ƛ y r} {z} d1 (alpha{t' = t'} ncap ne da su) (lam-go v1 v2 su') apart | p1 , p2
  with &&-elim{~ y' ∈ r1} apart
subst-⇒αβ {t1} {ƛ y t2} {r1} {ƛ y' r'} {ƛ y r} {z} d1 (alpha{t' = t'} ncap ne da su) (lam-go v1 v2 su') apart | p1 , p2 | a1 , a2
  with subst-⇒αβ d1 da su' (Apart-rename{r1} a2 su)
subst-⇒αβ {t1} {ƛ y t2} {r1} {ƛ y' r2} {ƛ y t} {z} d1 (alpha{t' = t2'} ncap ne da su) (lam-go v1 v2 su') apart | p1 , p2 | a1 , a2
  | q , sq , dq with Rename-subst su sq 
subst-⇒αβ {t1} {ƛ y t2} {r1} {ƛ y' r2} {ƛ y t} {z} d1 (alpha{t' = t2'} ncap ne da su) (lam-go v1 v2 su') apart | p1 , p2 | a1 , a2
  | q , sq , dq | w , sw1 , sw2 with keep (z ≃ y') 
subst-⇒αβ {t1} {ƛ y t2} {r1} {ƛ y' r2} {ƛ y t} {z} d1 (alpha{t' = t2'} ncap ne da su) (lam-go v1 v2 su') apart | p1 , p2 | a1 , a2
  | q , sq , dq | w , sw1 , sw2 | tt , eq = {!!}
subst-⇒αβ {t1} {ƛ y t2} {r1} {ƛ y' r2} {ƛ y t} {z} d1 (alpha{t' = t2'} ncap ne da su) (lam-go v1 v2 su') apart | p1 , p2 | a1 , a2
  | q , sq , dq | w , sw1 , sw2 | ff , eq = ƛ y' w , lam-go h (~-≡-tt{y' ∈ r1} a1) sw2 , alpha {!!} ne dq sw1 --
  where h : z ∈ ƛ y' r2 ≡ tt
        h = {!!}
subst-⇒αβ {t1} {ƛ y t2} {t1'} {ƛ y t2'} {ƛ y r} {z} d1 (lam d2) (lam-go v1 v2 s) apart | p1 , p2 with &&-elim{~ y ∈ t1'} apart
subst-⇒αβ {t1} {ƛ y t2} {t1'} {ƛ y t2'} {ƛ y r} {z} d1 (lam d2) (lam-go v1 v2 s) apart | p1 , p2 | apart1 , apart2 
  with subst-⇒αβ{t1}{t2}{t1'}{t2'}{r}{z} d1 d2 s apart2 | keep (z ∈ t2')
subst-⇒αβ {t1} {ƛ y t2} {t1'} {ƛ y t2'} {ƛ y r} {z} d1 (lam d2) (lam-go v1 v2 s) apart | p1 , p2 | apart1 , apart2 
  | q , sq , dq | tt , zi = ƛ y q , lam-go (&&-intro {~ z =ℕ y} p1 zi) (∉-⇒αβ v2 d1) sq , lam dq
subst-⇒αβ {t1} {ƛ y t2} {t1'} {ƛ y t2'} {ƛ y r} {z} d1 (lam d2) (lam-go v1 v2 s) apart | p1 , p2 | apart1 , apart2 
  | q , sq , dq | ff , zi with Subst-refl sq zi
subst-⇒αβ {t1} {ƛ y t2} {t1'} {ƛ y t2'} {ƛ y r} {z} d1 (lam d2) (lam-go v1 v2 s) apart | p1 , p2 | apart1 , apart2 
  | q , sq , dq | ff , zi | refl = ƛ y t2' , lam-stop (&&-ff-intro2 {~ z =ℕ y} zi) , lam dq
subst-⇒αβ{x = x} d1 (alpha{z}{z'}{t}{t'}{r} fr ne x₁ x₂) (lam-stop e) apart with &&-ff-elim{~ x =ℕ z} e
subst-⇒αβ{x = x} d1 (alpha{z}{z'}{t}{t'}{r} fr ne x₁ x₂) (lam-stop e) apart | inj₁ i with =ℕ-to-≡{x}{z} (~ff-≡{x =ℕ z} i)
subst-⇒αβ d1 (alpha{z}{z'}{t}{t'}{r} fr ne x₁ x₂) (lam-stop e) apart | inj₁ i | refl = ƛ z' r , lam-stop h , (alpha fr ne x₁ x₂)
 where h : ~ z =ℕ z' && z ∈ r ≡ ff
       h rewrite ne = var-∉-Subst {z} {var z'} ne x₂
subst-⇒αβ{x = x} d1 (alpha{z}{z'}{t}{t'}{r} fr ne x₁ x₂) (lam-stop e) apart | inj₂ i with keep (x ≃ z')
subst-⇒αβ{x = x} d1 (alpha{z}{z'}{t}{t'}{r} fr ne x₁ x₂) (lam-stop e) apart | inj₂ i | tt , p with =ℕ-to-≡{x}{z'} p 
subst-⇒αβ{x = x} d1 (alpha{z}{z'}{t}{t'}{r} fr ne x₁ x₂) (lam-stop e) apart | inj₂ i | tt , p | refl =
  ƛ x r , lam-stop h , alpha fr ne x₁ x₂
  where h : x ∈ (ƛ x r) ≡ ff
        h rewrite =ℕ-refl x = refl
subst-⇒αβ{x = x} d1 (alpha{z}{z'}{t}{t'}{r} fr ne x₁ x₂) (lam-stop e) apart | inj₂ i | ff , p = 
  ƛ z' r , lam-stop h , alpha fr ne x₁ x₂
  where h : x ∈ (ƛ z' r) ≡ ff
        h rewrite p = ∉-Subst{x}{z}{var z'}{t'}{r} p (∉-⇒αβ i x₁) x₂
subst-⇒αβ d1 (lam{t' = t'} x) (lam-stop{t}{v}{y}{s} e) apart with keep (v =ℕ y)
subst-⇒αβ d1 (lam{t' = t'} x) (lam-stop{t}{v}{y}{s} e) apart | tt , eq rewrite eq =
  ƛ y t' , lam-stop p , (lam x)
 where p : v ∈ (ƛ y t') ≡ ff
       p rewrite eq = refl 
subst-⇒αβ d1 (lam{t' = t'} x) (lam-stop{t}{v}{y}{s} e) apart | ff , eq rewrite eq =
  ƛ y t' , lam-stop ((&&-ff-intro2{~ v =ℕ y} (∉-⇒αβ e x))) , (lam x)

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