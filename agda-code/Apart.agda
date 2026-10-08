open import lib
open import VarInterface

module Apart(vi : VI) where

open VI vi

open import Tm vi
open import VarOps vi

Apart : Tm → 𝕃 V → 𝔹
Apart t vs = varapart vs (fvs t) 


