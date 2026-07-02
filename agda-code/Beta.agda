open import lib
open import relations
open import VarInterface

module Beta where

open import Tm 
open import Ctxt 
open import Subst 
open import Tau 

β : Rel Tm
β ((ƛ x t1) · t2) = Subst [] t2 x t1
β _ _ = ⊥

↝β : Rel Tm
↝β = τ β

deterministic-β : deterministic β
deterministic-β {(ƛ x t1) · t2} d1 d2  = substDeterministic d1 d2
