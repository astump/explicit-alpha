-- {-# OPTIONS --allow-unsolved-metas #-}
open import lib
open import bool-relations
open import functions

module VarInterface where

record VI : Set₁ where
  field
    V : Set
    _≃_ : V → V → 𝔹
    ≃-equivalence : equivalence _≃_
    ≃-≡ : computational-equality _≃_
