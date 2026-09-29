open import lib hiding (_>>=_ ; return ; _∘_)

module Stateful where

open import Monad

data Stateful(S V : Set) : Set where
  stateful : (S → V × S) → Stateful S V

returnStateful : ∀{S V : Set} → V → Stateful S V
returnStateful v = stateful (λ s → (v , s))

bindStateful : ∀{S A B : Set} → Stateful S A → (A → Stateful S B) → Stateful S B
bindStateful{S}{A}{B} (stateful f) g = stateful h
 where h : S → B × S
       h s with f s
       h s | (a , s') with g a
       h s | (a , s') | (stateful h) = h s'

runStateful : ∀{S V : Set} → Stateful S V → S → V × S
runStateful (stateful f) = f

evalStateful : ∀{S V : Set} → Stateful S V → S → V
evalStateful (stateful f) s = fst (f s)

instance
 StatefulMonad : ∀{S : Set} → Monad (Stateful S)
 StatefulMonad{S} = record { return = returnStateful ; _>>=_ = bindStateful }