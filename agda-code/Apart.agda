open import lib
open import VarInterface

module Apart where

open import Ctxt 
open import Tm 

infix 5 _∉_

-- x ∉ t means that x does not occur free in t
data _∉_ : V → Tm → Set where
 notinVar : ∀{x y : V} → 
             x ≃ y ≡ ff →
             x ∉ (var y)
 notinApp : ∀{x : V}
             {t1 t2 : Tm} → 
             x ∉ t1 →
             x ∉ t2 →              
             x ∉ (t1 · t2)
 notinLamBody : ∀{x y : V} 
             {t : Tm} →
             x ≃ y ≡ ff → 
             x ∉ t →
             x ∉ (ƛ y t)
 notinLamBound : ∀{x y : V} 
                {t : Tm} →
                x ≃ y ≡ tt → 
                x ∉ (ƛ y t)

Apart : Tm → Ctxt → Set
Apart t = all-pred (λ x → x ∉ t)

{-
Apart# : ∀{Γ : Ctxt}{x : V} →
          Apart (var x) Γ →
          x # Γ
Apart# {[]} A = #empty
Apart# {_ :: _} (notinVar x₁ , b) = #skip (Apart# b) (~≃-sym x₁)

Apartƛ1 : ∀{Γ : Ctxt}{x : V}{t : Tm} → 
         Apart (ƛ x t) Γ →
         Apart t Γ
Apartƛ1 {[]} A = triv
Apartƛ1 {_ :: _} (notinLam1 x₁ A , A') = A , Apartƛ1 A'

Apartƛ2 : ∀{Γ : Ctxt}{x : V}{t : Tm} → 
         Apart (ƛ x t) Γ →
         x # Γ
Apartƛ2 {[]} A = #empty
Apartƛ2 {_ :: _} (notinLam1 x A , A') = #skip (Apartƛ2 A') (~≃-sym x)

Apartƛ : ∀{Γ : Ctxt}{x : V}{t : Tm} → 
         Apart t Γ →
         x # Γ → 
         Apart (ƛ x t) Γ 
Apartƛ {[]} A g = triv
Apartƛ {_ :: _} (a , A) (#skip g n) = (notinLam1 (~≃-sym n) a) , Apartƛ A g

Apart1 : ∀{Γ : Ctxt}{t1 t2 : Tm} →
          Apart (t1 · t2) Γ →
          Apart t1 Γ
Apart1 {[]} A = triv
Apart1 {_ :: _} (notinApp A1 A2 , Q) = A1 , Apart1 Q

Apart2 : ∀{Γ : Ctxt}{t1 t2 : Tm} →
          Apart (t1 · t2) Γ →
          Apart t2 Γ
Apart2 {[]} A = triv
Apart2 {_ :: _} (notinApp A1 A2 , Q) = A2 , Apart2 Q

Apart· : ∀{Γ : Ctxt}{t1 t2 : Tm} →
          Apart t1 Γ →
          Apart t2 Γ →           
          Apart (t1 · t2) Γ
Apart· {[]} A1 A2 = triv
Apart· {_ :: _} (a1 , A1) (a2 , A2) = notinApp a1 a2 , Apart· A1 A2
-}