open import lib
open import relations
open import diamond
open import VarInterface

module Diamond(vi : VI) where

open VI vi
open import Ctxt vi
open import Tm vi
open import Subst vi
open import Beta vi
open import Alpha vi 
open import Parallel vi

{- a generic proof of the diamond property for parallel reduction, assuming that

   1. r commutes with ⇒c r, and
   2. r itself has the subdiamond property
-}
mutual 
 diamond-⇒ : ∀{r : ∀{Γ} → Rel (Tm Γ)} →
              ({Γ : Ctxt} → commute (r {Γ}) (⇒c r {Γ})) → 
              ({Γ : Ctxt} → subdiamond (r {Γ})) → 
              {Γ : Ctxt} → diamond (⇒ r {Γ})
 diamond-⇒ comm dr (⇒ctxt d) (⇒ctxt d') with diamond-⇒c comm dr d d'
 diamond-⇒ comm dr (⇒ctxt d) (⇒ctxt d') | , r , r' = , ⇒ctxt r , ⇒ctxt r'
 diamond-⇒ comm dr (⇒ctxt d) (⇒base d' s) with diamond-⇒c comm dr d d'
 diamond-⇒ comm dr (⇒ctxt d) (⇒base d' s) | , r , r' with comm s r' 
 diamond-⇒ comm dr (⇒ctxt d) (⇒base d' s) | , r , r' | , w , w' = , ⇒base r w' , ⇒ctxt w
 diamond-⇒ comm dr (⇒base d s) (⇒ctxt d') with diamond-⇒c comm dr d d' 
 diamond-⇒ comm dr (⇒base d s) (⇒ctxt d') | , r , r' with comm s r
 diamond-⇒ comm dr (⇒base d s) (⇒ctxt d') | , r , r' | , w , w' = , ⇒ctxt w , ⇒base r' w'
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') with diamond-⇒c comm dr d d' 
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') | , r , r' with comm s r | comm s' r' 
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') | , r , r' | , w , w' | , u , u' with dr u' w' 
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') | , r , r' | , w , w' | , u , u' | inj₁ refl = , ⇒ctxt w , ⇒ctxt u
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') | , r , r' | , w , w' | , u , u' | inj₂ (, z , z') = , ⇒base w z' , ⇒base u z 
 diamond-⇒c : ∀{r : ∀{Γ} → Rel (Tm Γ)} → 
              ({Γ : Ctxt} → commute (r {Γ}) (⇒c r {Γ})) → 
              ({Γ : Ctxt} → subdiamond (r {Γ})) → 
              {Γ : Ctxt} → diamond (⇒c r {Γ})
 diamond-⇒c comm dr ⇒var ⇒var = , ⇒var , ⇒var
 diamond-⇒c comm dr (⇒app d1 d2) (⇒app d1' d2') with diamond-⇒ comm dr d1 d1' | diamond-⇒ comm dr d2 d2'
 diamond-⇒c comm dr (⇒app d1 d2) (⇒app d1' d2') | , r1 , r1' | , r2 , r2' = , ⇒app r1 r2 , ⇒app r1' r2'
 diamond-⇒c comm dr (⇒lam d) (⇒lam d') with diamond-⇒ comm dr d d'
 diamond-⇒c comm dr (⇒lam d) (⇒lam d') | , r , r' = , ⇒lam r , ⇒lam r' 


{-
Subst-⇒ : ∀{Γ : Ctxt}{t2 t2' : Tm Γ}{x y : V}{t1 t1' : Tm (x :: Γ)}{m : Tm Γ →
            Subst t2 x t1 m →
            t2 ⟨ ⇒ β ⟩ t2' →
            ƛ y t1 ⟨ ⇒ β ⟩ t1' →            
            m ⟨ ⇒ β ⟩ (t1' · t2')
-}

commute-β : ∀{Γ : Ctxt} → commute (β {Γ}) (⇒c β {Γ}) 
commute-β s (⇒app {t1 = ƛ y t1} d1 d2) = {!!}

subdiamond-β : ∀{Γ : Ctxt} → subdiamond (β {Γ})
subdiamond-β{Γ}{(ƛ y t1) · t2}{r1}{r2} s s' = inj₁ (substDeterministic s s')

diamond-⇒β : ∀{Γ : Ctxt} → diamond (⇒ β {Γ})
diamond-⇒β = diamond-⇒{β} {!!} λ{Γ}{x : Tm Γ} → subdiamond-β{Γ}{x}

{-
confluent-↝αβ : confluent ↝αβ
confluent-↝αβ = mediator-diamond ↝αβ-⇒ ⇒-↝αβ⋆ diamond-⇒-}