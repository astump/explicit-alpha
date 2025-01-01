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

   1. all peaks with r and ⇒c r can be completed with ⇒ r and r.
   2. r is deterministic
-}
mutual 
 diamond-⇒ : ∀{r : Rel Tm} →
              (square r (⇒c r) (⇒ r) r) → 
              deterministic r → 
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
 diamond-⇒ comm dr (⇒base d s) (⇒base d' s') | , m , m' | , w , w' | , u , u' rewrite dr w' u' = , w , u

 diamond-⇒c : ∀{r : Rel Tm} → 
              (square r (⇒c r) (⇒ r) r) → 
              deterministic r → 
              diamond (⇒c r)
 diamond-⇒c comm dr ⇒var ⇒var = , ⇒var , ⇒var
 diamond-⇒c comm dr (⇒app d1 d2) (⇒app d1' d2') with diamond-⇒ comm dr d1 d1' | diamond-⇒ comm dr d2 d2'
 diamond-⇒c comm dr (⇒app d1 d2) (⇒app d1' d2') | , r1 , r1' | , r2 , r2' = , ⇒app r1 r2 , ⇒app r1' r2'
 diamond-⇒c comm dr (⇒lam d) (⇒lam d') with diamond-⇒ comm dr d d'
 diamond-⇒c comm dr (⇒lam d) (⇒lam d') | , r , r' = , ⇒lam r , ⇒lam r' 

square-β : square β (⇒c β) (⇒ β) β
square-β (substVarFound A) (⇒app (⇒ctxt (⇒lam (⇒base ⇒var ()))) d2)
square-β (substVarFound A) (⇒app (⇒ctxt (⇒lam (⇒ctxt ⇒var))) d2) = , d2 , substVarFound ({!!} {- Apart-⇒β  A d2-})
square-β (substVarFound A) (⇒app (⇒base (⇒lam (⇒base ⇒var ())) d1') d2)
square-β (substVarNot ne) (⇒app (⇒ctxt (⇒lam (⇒base ⇒var ()))) d2) 
square-β (substVarNot ne) (⇒app (⇒ctxt (⇒lam (⇒ctxt ⇒var))) d2) = , ⇒ctxt ⇒var , substVarNot ne
square-β (substVarNot ne) (⇒app (⇒base (⇒lam d1) ()) d2)
square-β (substApp s1 s2) (⇒app {t1 = ƛ y t1} d1 d2) = {!!}
square-β (substLam s) (⇒app {t1 = ƛ y t1} d1 d2) = {!!}

diamond-⇒β : diamond (⇒ β)
diamond-⇒β = diamond-⇒{β} square-β λ{x : Tm} → deterministic-β{x}

confluent-↝β : confluent ↝β
confluent-↝β = mediator-diamond τ⇒ ⇒τ⋆ diamond-⇒β

commute-parallel : ∀{ρ : Renaming} →
                    commute (⇒ β) (Alpha ρ)
commute-parallel {ρ} {t} {t1} {t2} (⇒ctxt x) d2 = {!!}
commute-parallel {ρ} {t} {t1} {t2} (⇒base x x₁) d2 = {!!}