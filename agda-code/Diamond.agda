open import lib hiding (square)
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
 diamond-⇒ : ∀{r : Rel Tm} →
              (square r (⇒c r) (⇒ r) r) → 
              (subdiamond (r)) → 
              diamond (⇒ r)
 diamond-⇒ comm dr (⇒ctxt d) (⇒ctxt d') with diamond-⇒c comm dr d d'
 diamond-⇒ comm dr (⇒ctxt d) (⇒ctxt d') | , r , r' = , ⇒ctxt r , ⇒ctxt r'
 diamond-⇒ comm dr (⇒ctxt d) (⇒base d' s) with diamond-⇒c comm dr d d'
 diamond-⇒ comm dr (⇒ctxt d) (⇒base d' s) | , r , r' with comm s r' 
 diamond-⇒ comm dr (⇒ctxt d) (⇒base d' s) | , r , r' | , w , w' = , ⇒base r w' , w
 diamond-⇒ comm dr (⇒base d s) (⇒ctxt d') with diamond-⇒c comm dr d d' 
 diamond-⇒ comm dr (⇒base d s) (⇒ctxt d') | , r , r' with comm s r
 diamond-⇒ comm dr (⇒base d s) (⇒ctxt d') | , r , r' | , w , w' = , w , ⇒base r' w'
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') with diamond-⇒c comm dr d d' 
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') | , m , m' with comm s m | comm s' m' 
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') | , m , m' | , w , w' | , u , u' = , {!!} , {!!}
{-
with dr u' w' 
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') | , r , r' | , w , w' | , u , u' | inj₁ refl = , ⇒ctxt w , ⇒ctxt u
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') | , r , r' | , w , w' | , u , u' | inj₂ (, z , z') = , ⇒base w z' , ⇒base u z 
-}
 diamond-⇒c : ∀{r : Rel Tm} → 
              (square r (⇒c r) (⇒ r) r) → 
              (subdiamond (r)) → 
              diamond (⇒c r)
 diamond-⇒c comm dr ⇒var ⇒var = , ⇒var , ⇒var
 diamond-⇒c comm dr (⇒app d1 d2) (⇒app d1' d2') with diamond-⇒ comm dr d1 d1' | diamond-⇒ comm dr d2 d2'
 diamond-⇒c comm dr (⇒app d1 d2) (⇒app d1' d2') | , r1 , r1' | , r2 , r2' = , ⇒app r1 r2 , ⇒app r1' r2'
 diamond-⇒c comm dr (⇒lam d) (⇒lam d') with diamond-⇒ comm dr d d'
 diamond-⇒c comm dr (⇒lam d) (⇒lam d') | , r , r' = , ⇒lam r , ⇒lam r' 


commute-β : commute (β) (⇒c β) 
commute-β s (⇒app {t1 = ƛ y t1} d1 d2) = {!!}

subdiamond-β : subdiamond (β)
subdiamond-β{(ƛ y t1) · t2}{r1}{r2} s s' = inj₁ (substDeterministic s s')

diamond-⇒β : diamond (⇒ β)
diamond-⇒β = diamond-⇒{β} {!!} λ{x : Tm} → subdiamond-β{x}

{-
confluent-↝αβ : confluent ↝αβ
confluent-↝αβ = mediator-diamond ↝αβ-⇒ ⇒-↝αβ⋆ diamond-⇒-}