open import lib
open import relations as R
open import diamond
open import VarInterface

module Renaming where

open import Tm 

Renaming : Set
Renaming = 𝕃 (V × V)

domr : Renaming → 𝕃 V
domr = map fst

ranr : Renaming → 𝕃 V
ranr = map snd

lookupr : Renaming → V → maybe V
lookupr [] x = nothing
lookupr ((x' , y) :: ρ) x =
  if (x ≃ x') then just y
  else lookupr ρ x 

rename : Renaming → V → V
rename r v with lookupr r v
rename r v | nothing = v
rename r v | just v' = v'

