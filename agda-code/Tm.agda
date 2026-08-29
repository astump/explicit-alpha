open import lib
open import VarInterface

module Tm where

data Tm : Set where
  var : V → Tm 
  _·_ : (t1 t2 : Tm) → Tm 
  ƛ : (x : V) → (t : Tm) → Tm 

infixl 9 _·_ 
infixl 8 ƛ

fvs : Tm → 𝕃 V
fvs (var x) = [ x ]
fvs (t1 · t2) = fvs t1 ++ fvs t2
fvs (ƛ x t) = remove _≃_ x (fvs t)

infix 8 _∈_

-- x ∈ t means x occurs free in t
_∈_ : V → Tm → 𝔹
x ∈ t = varmem x (fvs t)

bvs : Tm → 𝕃 V
bvs (var x) = []
bvs (t · t₁) = bvs t ++ bvs t₁ 
bvs (ƛ x t) = x :: bvs t

∈var : ∀{x y : V}{b : 𝔹} →
       x ∈ var y ≡ b →
       x ≃ y ≡ b
∈var{x}{y}{b} eq with(x ≃ y)
∈var{x}{y}{b} eq | tt = eq
∈var{x}{y}{b} eq | ff = eq

∈· : ∀{x : V}{t1 t2 : Tm} →
     x ∈ t1 · t2 ≡ ff →
     x ∈ t1 ≡ ff ∧ x ∈ t2 ≡ ff
∈·{x}{t1}{t2} eq rewrite varmem-++ x (fvs t1)(fvs t2) = (||≡ff₁ eq) , (||≡ff₂ eq)

∈ƛ : ∀{x y : V}{t : Tm} →
     x ∈ ƛ y t ≡ tt →
     x ≃ y ≡ ff ∧ x ∈ t ≡ tt 
∈ƛ{x}{y}{t} u = varmem-remove{x}{y}{fvs t} u


∈ƛ· : ∀{x y : V}{t1 t2 : Tm} →
     x ∈ ƛ y (t1 · t2) ≡ ff → 
     x ∈ ƛ y t1 ≡ ff ∧ x ∈ ƛ y t2 ≡ ff
∈ƛ·{x}{y}{t1}{t2} eq with keep (x ≃ y)
∈ƛ·{x}{y}{t1}{t2} eq | tt , eq' rewrite ≃-≡{x} eq' | varmem-remove-same{y}{fvs t1} | varmem-remove-same{y}{fvs t2} =
 refl , refl
∈ƛ·{x}{y}{t1}{t2} eq | ff , eq'
  rewrite varmem-remove-neq{x}{y}{fvs t1 ++ fvs t2} eq' | varmem-++ x (fvs t1) (fvs t2)
        | varmem-remove-neq{x}{y}{fvs t1} eq' | varmem-remove-neq{x}{y}{fvs t2} eq' = ||-≡-ff{varmem x (fvs t1)} eq

∈ƛƛ : ∀{x y z : V}{t : Tm} →
     x ∈ ƛ y (ƛ z t) ≡ ff → 
     x ≃ y ≡ tt ∨ x ≃ z ≡ tt ∨ x ∈ t ≡ ff
∈ƛƛ{x}{y}{z}{t} e with keep (x ≃ y)
∈ƛƛ{x}{y}{z}{t} e | tt , eq rewrite eq = inj₁ refl
∈ƛƛ{x}{y}{z}{t} e | ff , eq rewrite eq with keep (x ≃ z)
∈ƛƛ{x}{y}{z}{t} e | ff , eq | tt , eq' rewrite eq' = inj₂ (inj₁ refl)
∈ƛƛ{x}{y}{z}{t} e | ff , eq | ff , eq' rewrite eq' | varmem-remove-neq{x}{y}{varrem z (fvs t)} eq
                                             | varmem-remove-neq{x}{z}{fvs t} eq' = inj₂ (inj₂ e)