{-# OPTIONS --allow-unsolved-metas #-}
open import lib
open import VarInterface

module Subst where

open import Tm 
open import Substitution 
open import Apart

data Subst : Tm → V → Tm → Tm → Set where
  var-found : ∀{t : Tm}{v : V} → 
              Subst t v (var v) t
  var-not : ∀{t : Tm}{v x : V} →
             v ≃ x ≡ ff → 
             Subst t v (var x) (var x)
  app : ∀{t : Tm}{v : V}
         {t1 t2 t1' t2' : Tm} → 
         Subst t v t1 t1' →
         Subst t v t2 t2' →
         Subst t v (t1 · t2) (t1' · t2')
  lam-go : ∀{t : Tm}{v : V}{x : V}{s s' : Tm} →
           v ∈ (ƛ x s) ≡ tt →
           x ∈ t ≡ ff →                 -- avoid capture
           Subst t v s s' →
           Subst t v (ƛ x s) (ƛ x s')
  lam-stop : ∀{t : Tm}{v : V}{x : V}{s : Tm} →
             v ∈ (ƛ x s) ≡ ff →
             Subst t v (ƛ x s) (ƛ x s)

∉-Subst : ∀{x y : V}{t1 t2 r : Tm} →
          x ∈ t1 ≡ ff →
          x ∈ t2 ≡ ff →
          Subst t1 y t2 r →
          x ∈ r ≡ ff
∉-Subst {x} {y} {t1} {t2} {r} e1 e2 var-found = e1
∉-Subst {x} {y} {t1} {var z} {var z} e1 e2 (var-not x₁) = e2
∉-Subst {x} {y} {t1} {ta · tb} {r1 · r2} e1 e2 (app s1 s2) with ||-≡-ff{x ∈ ta} e2
∉-Subst {x} {y} {t1} {ta · tb} {r1 · r2} e1 e2 (app s1 s2) | ea , eb rewrite ∉-Subst e1 ea s1 = ∉-Subst e1 eb s2
∉-Subst {x} {y} {t1} {ƛ z t2} {ƛ z r} e1 e2 (lam-go x₁ x₂ s) with &&-ff-elim{~ x =ℕ z} e2
∉-Subst {x} {y} {t1} {ƛ z t2} {ƛ z r} e1 e2 (lam-go x₁ x₂ s) | inj₁ i rewrite i = refl
∉-Subst {x} {y} {t1} {ƛ z t2} {ƛ z r} e1 e2 (lam-go x₁ x₂ s) | inj₂ i rewrite ∉-Subst e1 i s | &&-ff (~ x =ℕ z) = refl
∉-Subst {x} {y} {t1} {t2} {r} e1 e2 (lam-stop x₁) = e2

var-∉-Subst : ∀{y : V}{t1 t2 r : Tm} →
              y ∈ t1 ≡ ff →
              Subst t1 y t2 r →
              y ∈ r ≡ ff
var-∉-Subst {y} {t1} {t2} {r} e var-found = e
var-∉-Subst {y} {t1} {t2} {r} e (var-not x) = x
var-∉-Subst {y} {t1} {ta · tb} {ta' · tb'} e (app s s₁) rewrite var-∉-Subst e s | var-∉-Subst e s₁ = refl
var-∉-Subst {y} {t1} {ƛ a s} {ƛ a s'} e (lam-go x x₁ u) rewrite var-∉-Subst e u | &&-ff (~ y =ℕ a) = refl
var-∉-Subst {y} {t1} {t2} {r} e (lam-stop x) = x

Subst-refl : ∀{t1 : Tm}{x : V}{t2 r : Tm} →
             Subst t1 x t2 r →
             x ∈ t2 ≡ ff →
             t2 ≡ r
Subst-refl {t1} {x} {t2} {r} var-found e rewrite =ℕ-refl x with e
Subst-refl {t1} {x} {t2} {r} var-found e | ()
Subst-refl {t1} {x} {t2} {r} (var-not x₁) e = refl
Subst-refl {t1} {x} {ta · tb} {ta' · tb'} (app s s₁) e with ||-ff-elim{x ∈ ta} e 
Subst-refl {t1} {x} {ta · tb} {ta' · tb'} (app s s₁) e | p1 , p2 rewrite Subst-refl s p1 | Subst-refl s₁ p2  = refl
Subst-refl {t1} {x} {ƛ y t2} {ƛ y r} (lam-go x₁ x₂ s) e rewrite e with x₁ 
Subst-refl {t1} {x} {ƛ y t2} {ƛ y r} (lam-go x₁ x₂ s) e | ()
Subst-refl {t1} {x} {t2} {r} (lam-stop x₁) e = refl

Apart-rename : ∀{s t r : Tm}{y y' : V} →
               Apart s (bvs r) ≡ tt →
               Subst (var y') y t r → 
               Apart s (bvs t) ≡ tt 
Apart-rename {s} {t} {r} {y} {y'} apart var-found = refl
Apart-rename {s} {t} {r} {y} {y'} apart (var-not x) = refl
Apart-rename {s} {t1 · t2} {t1' · t2'} {y} {y'} apart (app su su₁) rewrite list-all-append (λ v → ~ v ∈ s) (bvs t1) (bvs t2) |
  list-all-append (λ v → ~ v ∈ s) (bvs t1') (bvs t2') with &&-elim{Apart s (bvs t1')} apart 
Apart-rename {s} {t1 · t2} {t1' · t2'} {y} {y'} apart (app su su₁) | apart1 , apart2 
  rewrite Apart-rename{s} apart1 su |  Apart-rename{s} apart2 su₁ =  refl
Apart-rename {s} {ƛ z t} {ƛ z r} {y} {y'} apart (lam-go x x₁ su) with &&-elim {~ z ∈ s} apart
Apart-rename {s} {ƛ z t} {ƛ z r} {y} {y'} apart (lam-go x x₁ su) | p1 , p2 rewrite p1 = Apart-rename{s} p2 su
Apart-rename {s} {ƛ z t} {ƛ z t} {y} {y'} apart (lam-stop x) = apart

substLem : ∀{t s : Tm}{x : V} →
           Apart t (bvs s) ≡ tt → 
           Subst t x s (graft1 t x s)
substLem {t} {var y}   {x} ap with keep (x ≃ y)
substLem {t} {var y}   {x} ap | tt , eq rewrite ≃-≡{x} eq | ≃-refl{y} = var-found
substLem {t} {var y}   {x} ap | ff , eq rewrite ~≃-sym{x} eq = var-not eq
substLem {t} {t1 · t2} {x} ap = app (substLem {t} {t1} {x} (Apart-++1{t}{bvs t1}{bvs t2} ap))
                                    (substLem {t} {t2} {x} (Apart-++2{t}{bvs t1}{bvs t2} ap))
substLem {t} {ƛ y t1}  {x} ap with keep (x ≃ y)
substLem {t} {ƛ y t1}  {x} ap | tt , eq rewrite eq | graft-[]{t1} = lam-stop h
 where h : ~ x ≃ y && x ∈ t1 ≡ ff
       h rewrite eq = refl
substLem {t} {ƛ y t1}  {x} ap | ff , eq rewrite eq with keep (x ∈ t1)
substLem {t} {ƛ y t1}  {x} ap | ff , eq | tt , eq' =
  lam-go (&&-intro{~ x ≃ y} (~-≡-ff eq) eq') (~-≡-tt (&&-elim1 ap)) (substLem{t}{t1}{x} (&&-elim2 ap))
substLem {t} {ƛ y t1}  {x} ap | ff , eq | ff , eq' rewrite graft-~∈{x}{t}{t1} eq' = lam-stop (&&-ff-intro2{~ x ≃ y} eq')

