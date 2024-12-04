open import lib
open import VarInterface

module Apart(vi : VI) where

open VI vi
open import Ctxt vi
open import Tm vi

-- Apart t Γ means that no free variable of t is in Γ
data Apart : Tm → Ctxt → Set where
 apartVar : ∀{Γ : Ctxt}{v : V}
             (a : v # Γ) →
             Apart (var v) Γ
 apartApp : ∀{Γ : Ctxt}{t1 t2 : Tm} → 
             Apart t1 Γ →
             Apart t2 Γ →              
             Apart (t1 · t2) Γ
 apartLam : ∀{Γ : Ctxt}{x : V} 
             {t : Tm} → 
             Apart t (ctxtDrop x Γ) →
             Apart (ƛ x t) Γ





-- x ∉ t means that x does not occur at all (free or bound) in t
data _∉_ : V → Tm → Set where
 apartVar : ∀{x y : V} → 
             x ≃ y ≡ ff →
             x ∉ (var y)
 apartApp : ∀{x : V}
             {t1 t2 : Tm} → 
             x ∉ t1 →
             x ∉ t2 →              
             x ∉ (t1 · t2)
 apartLam : ∀{x y : V} 
             {t : Tm} →
             x ≃ y ≡ ff → 
             x ∉ t →
             x ∉ (ƛ y t)

