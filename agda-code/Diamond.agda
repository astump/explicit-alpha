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

diamond-⇒ : ∀{Γ : Ctxt} → diamond (⇒{Γ})
diamond-⇒ ⇒var ⇒var = , ⇒var , ⇒var
diamond-⇒ (⇒app d1 d2) (⇒app d1' d2') with diamond-⇒ d1 d1' | diamond-⇒ d2 d2'
diamond-⇒ (⇒app d1 d2) (⇒app d1' d2') | , r1 , r2 | , r1' , r2' = , ⇒app r1 r1' , ⇒app r2 r2'
diamond-⇒ (⇒app (⇒lam d1) d2) (⇒beta d1' d2' be) = {!!}
diamond-⇒ (⇒lam d) (⇒lam d') with diamond-⇒ d d'
diamond-⇒ (⇒lam d) (⇒lam d') | , r1 , r2 = , ⇒lam r1 , ⇒lam r2
diamond-⇒ (⇒beta d1 d2 be) (⇒app (⇒lam d1') d2') = {!!}
diamond-⇒ (⇒beta d1 d2 be) (⇒beta d1' d2' be') with diamond-⇒ d1 d1' | diamond-⇒ d2 d2'
diamond-⇒ (⇒beta d1 d2 be) (⇒beta d1' d2' be') | , r1 , r2 | , r1' , r2' = , {!!} , {!!}
{-
confluent-↝αβ : confluent ↝αβ
confluent-↝αβ = mediator-diamond ↝αβ-⇒ ⇒-↝αβ⋆ diamond-⇒-}