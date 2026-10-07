open import lib hiding (_>>=_ ; return ; _∘_)
open import VarInterface
open import VarImpls

module AlphaCanon where

open VI VI-𝕃𝔹

open import VarOps VI-𝕃𝔹
open import Tm VI-𝕃𝔹
open import Renaming VI-𝕃𝔹

{- PathDistinct vs t

   This means that the variables in vs are not bound in t
   and hereditarily for subterms of t where we add the bound
   variables above those subterms, to vs.

   So if x is bound somewhere in t, then it cannot be bound again
   below that point.

   This explains the name: the bound variables along each path into
   the term are distinct (and different from the variables in vs)
-}
data PathDistinct : 𝕃 V → Tm → Set where
 var : ∀{vs : 𝕃 V}{x : V} → varmem x vs ≡ tt → PathDistinct vs (var x)
 app : ∀{vs : 𝕃 V}{t1 t2 : Tm} →
       PathDistinct vs t1 → 
       PathDistinct vs t2 →
       PathDistinct vs (t1 · t2)
 lam : ∀{vs : 𝕃 V}{x : V}{t : Tm} → 
       varmem x vs ≡ ff →
       PathDistinct (x :: vs) t →
       PathDistinct vs (ƛ x t)

{- all bound variables are distinct from each other and all the
   free variables.

   The implementation collects the list of all bound variables
   by binding occurrence, and then insists that there are no duplicates.
   So the same variable cannot be bound twice.
-}
AllDistinct : 𝕃 V → Tm → Set
AllDistinct vs t = varunique (bvs t) ≡ tt ∧ PathDistinct vs t 

{- αc n ρ t

   Free variables in t are renamed by ρ.  Bound variables are
   chosen to be distinct from each other and bigger than n.
   This means that if n is an upper bound on the free variables
   of t, then the bound variables will be distinct from the free
   ones in the output term.

   The main idea is to rename variables in the left parts of applications
   differently from those in the right parts, by adding tt to n on one
   side, and ff on the other. -}
αc : V → Renaming → Tm → Tm
αc n ρ (var x) = var (rename ρ x)
αc n ρ (t1 · t2) = αc (ff :: n) ρ t1 · αc (tt :: n) ρ t2
αc n ρ (ƛ x t) =
 ƛ n (αc (ff :: n) ((x , n) :: ρ) t)

