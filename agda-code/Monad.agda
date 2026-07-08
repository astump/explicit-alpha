module Monad where

open import lib hiding (return ; _>>=_)

record Monad(M : Set → Set) : Set₁ where
  infixr 8 _>>=_
  field
    return : ∀{A : Set} → A → M A
    _>>=_ : ∀{A B : Set} → M A → (A → M B) → M B

open Monad {{ ... }} public