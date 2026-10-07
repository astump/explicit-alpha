open import lib hiding (_>>=_ ; return ; _∘_)
open import VarInterface
open import VarImpls

module Fresh where

open VI VI-𝕃𝔹
-- compute an upper bound of two variables. Longer
-- variables are bigger than shorter ones, and
-- tt is bigger than ff.
ubvar : V → V → V
ubvar [] [] = []
ubvar [] (x :: vs') = x :: vs'
ubvar (x :: vs) [] = x :: vs
ubvar (x :: vs) (y :: vs') = (x || y) :: ubvar vs vs'

-- compute an upper bound on all the variables in the input list
ubvars : 𝕃 V → V
ubvars = foldr ubvar []

-- compute a variable that is fresh with respect to the input list
fresh : 𝕃 V → V
fresh vs = ff :: ubvars vs

-- we order variables by the suffix relation.  So you can think of
-- variables as extended at the head of the list
Varle : V → V → Set
Varle v1 v2 = Suffix v1 v2 

Varlt : V → V → Set
Varlt v1 v2 = Varle v1 v2 ∧ v1 ≢ v2

Vargt : V → V → Set
Vargt n v = Varlt v n

Ubounded : 𝕃 V → V → Set
Ubounded vs n = all-pred (Vargt n) vs

Wlbounded : 𝕃 V → V → Set
Wlbounded vs n = all-pred (Varle n) vs
