open import lib
open import relations
open import VarInterface

module Beta (vi : VI) where

open VI vi

open import Tm vi
open import Subst vi 
open import Tau vi

β : Rel Tm
β ((ƛ x t1) · t2) = Subst t2 x t1
β _ _ = ⊥

↝β : Rel Tm
↝β = τ β

