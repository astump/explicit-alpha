open import lib
open import relations as R
open import diamond
open import VarInterface

module Renaming where

open import Tm 
open import Ctxt 
open import Beta 
open import Apart
open import Subst
open import Tau 

Renaming : Set
Renaming = 𝕃 (V × V)

renaming-dom : Renaming → 𝕃 V
renaming-dom = map fst

renaming-ran : Renaming → 𝕃 V
renaming-ran = map snd

lookup : Renaming → V → maybe V
lookup [] x = nothing
lookup ((x' , y) :: ρ) x =
  if (x ≃ x') then just y
  else lookup ρ x 

rename : Renaming → V → V
rename r v with lookup r v
rename r v | nothing = v
rename r v | just v' = v'

-- this applies the renaming without avoiding capture
graftr : Renaming → Tm → Tm
graftr r (var x) = var (rename r x)
graftr r (t · t') = graftr r t · graftr r t'
graftr r (ƛ x t) = ƛ x (graftr r t)