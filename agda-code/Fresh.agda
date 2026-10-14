open import lib hiding (_>>=_ ; return ; _∘_)
open import VarInterface
open import VarImpls

module Fresh where

open VI VI-𝕃𝔹
open import VarOps VI-𝕃𝔹

{- compute a variable Q that is fresh with respect to the input list of variables.
   Q will not be greater than (Vargt) those variables
   but any variable that is greater than or equal to Q will be guaranteed
   to be different (≢) from the variables in vs.

   We just create a new variable consisting of n + 1 copies of ff,
   where n is the max length of a variable in vs.
-}
fresh : 𝕃 V → V
fresh vs = ff :: foldr longer-list [] vs 

-- we order variables by the suffix relation.  So you can think of
-- variables as extended at the head of the list
Varle : V → V → Set
Varle v1 v2 = Suffix v1 v2 

Varlt : V → V → Set
Varlt v1 v2 = Varle v1 v2 ∧ v1 ≢ v2

Vargt : V → V → Set
Vargt n v = Varlt v n

{- the notion of upper bounding is a little subtle.
   We say that vs is upper-bounded by n iff no element
   of vs is in the upset of n.

   We take this definition so that we do not need the
   elements of vs to be smaller than n.

   We just need to make sure that everything bigger than
   n is not in vs.
-}
Ubounded : 𝕃 V → V → Set
Ubounded vs n = ∀{v : V} → Varle n v → varmem v vs ≡ ff

Wlbounded : 𝕃 V → V → Set
Wlbounded vs n = all-pred (Varle n) vs
