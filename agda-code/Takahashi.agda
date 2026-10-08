{-# OPTIONS --allow-unsolved-metas #-}
-- 
{- The function proposed by Takahashi to compute the maximum
   parallel reduct of t.
-}
open import lib hiding (_>>=_ ; return ; _∘_)
open import relations
open import VarInterface
open import VarImpls

module Takahashi where

open VI VI-𝕃𝔹

open import Tm VI-𝕃𝔹
open import Substitution VI-𝕃𝔹 
open import Renaming VI-𝕃𝔹
open import AlphaCanon 


tk : Tm → Tm
tk (var x) = var x
tk (var x · t) = var x · tk t
tk ((t1 · t2) · t3) = (tk (t1 · t2)) · tk t3
tk ((ƛ x t1) · t2) = graft1 (tk t2) x (tk t1)
tk (ƛ x t) = ƛ x (tk t)

αtk : V → Renaming → Tm → Tm
αtk n ρ t = tk (αc n ρ t)

-- a related function, for computing the superdevelopment of t
sd : Tm → Tm
sd (var x) = var x
sd (t1 · t2) with sd t1
sd (t1 · t2) | ƛ x t1' = graft1 (sd t2) x t1'
sd (t1 · t2) | var x = var x · (sd t2)
sd (t1 · t2) | ta · tb = ta · tb · (sd t2)
sd (ƛ x t) = ƛ x (sd t)


