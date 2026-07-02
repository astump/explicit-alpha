open import lib hiding (_>>=_ ; return )
open import relations as R
open import diamond
open import VarInterface
open import Monad

module Alpha where

open import Tm 
open import Ctxt 
open import Beta 
open import Apart
open import Subst
open import Tau 
open import Renaming 

----------------------------------------------------------------------
-- put terms in α-canonical form

AlphaM : Set → Set
AlphaM A = 𝕃 V → Renaming → A × 𝕃 V × Renaming

_>>=a_ : ∀{A B : Set} → AlphaM A → (A → AlphaM B) → AlphaM B
_>>=a_{A}{B} x f = λ vs r → h (x vs r)
 where h : A × 𝕃 V × Renaming → B × 𝕃 V × Renaming
       h (a , vs' , r') = f a vs' r'

returna : ∀{A : Set} → A → AlphaM A
returna a vs r = a , vs , r

getVars : AlphaM (𝕃 V)
getVars = λ vs r → vs , vs , r

getRenaming : AlphaM Renaming
getRenaming = λ vs r → r , vs , r

freshVar : AlphaM V
freshVar = λ vs r → let q = fresh vs in
                      q , q :: vs , r

setRenaming : Renaming → AlphaM ⊤
setRenaming r = λ vs _ → triv , vs , r

instance
  AMonad : Monad AlphaM
  AMonad = record { return = returna ; _>>=_ = _>>=a_ }

αcanon : Tm → AlphaM Tm
αcanon (var x) =
  do
    r ← getRenaming
    return (var (rename r x))
αcanon (t1 · t2) =
  do
    r1 ← αcanon t1
    r2 ← αcanon t2
    return (r1 · r2)
αcanon (ƛ x t) = 
  do
    q ← freshVar
    r ← getRenaming
    _ ← setRenaming ((x , q) :: r)
    b ← αcanon t
    return (ƛ q b)

-- rename the bound variables of t away from all variables of t
αcanont : Tm → Tm
αcanont t = fst (αcanon t (vars t) [])

----------------------------------------------------------------------
-- bare α
--
-- It is required that we can safely substitute the second variable
-- for the first.  This ensures we are avoiding capture.

α : Rel Tm
α (ƛ x t1) (ƛ x' t1') = Subst [] (var x') x t1 t1'
α _ _ = ⊥

↝α : Rel Tm
↝α = τ α
