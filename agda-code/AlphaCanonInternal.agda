{-# OPTIONS --allow-unsolved-metas #-}
open import lib hiding (_>>=_ ; return ; _∘_)
open import relations
open import functions
open import diamond
open import VarInterface

module AlphaCanonInternal where

open import Tm 
open import Renaming
open import Subst
open import Substitution hiding (_∘_)
open import Monad
open import AlphaM


