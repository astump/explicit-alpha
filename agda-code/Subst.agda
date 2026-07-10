open import lib
open import VarInterface

module Subst where

open import Tm 

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


{-
Subst-removed : ∀ {x y : V}{t1 t2 r : Tm} →
                Subst (var x) y t1 t2 →
                Subst r y t2 t2
Subst-removed = {!!}
-}

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