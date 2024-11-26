open import lib
open import relations as R
open import VarInterface

module Alpha(vi : VI) where

open VI vi
open import Tm vi
open import Ctxt vi
open import Weaken vi
open import Subst vi
open import Tau vi

{- (ƛ x t1) and (ƛ y t1') are α-equivalent iff
   we can rename y to x in t1 and get t1'.  To apply the substitution,
   though, we need to make sure that we can weaken in y and then exchange
   it with x, in the typing of t1 -}

α : ∀{Γ : Ctxt} → Rel (Tm Γ)
α{Γ} (ƛ x t1) (ƛ y t1') = 

  Σ[ t2 ∈ Tm (x :: y :: Γ) ] Weaken{[ x ]}{[ y ]}{Γ} t1 t2 ∧

  Subst{[]} (var y foundInCtxt) x t2 t1'

α _ _ = ⊥

↝α : ∀{Γ : Ctxt} → Rel (Tm Γ)
↝α = τ α

{-
=α : ∀{Γ : Ctxt} → Rel (Tm Γ)
=α = ↝α ⋆
-}

----------------------------------------------------------------------
-- Theorems about α
----------------------------------------------------------------------

α-symm : ∀{Γ : Ctxt} → R.symmetric (α{Γ})
α-symm {Γ}{ƛ x t1} {ƛ y t1'} (tw , w , s) =
  {!!} , {!!} , {!!} 


{-
↝α-symm : ∀{Γ : Ctxt} → R.symmetric (↝α{Γ})
↝α-symm = τ-symm α-symm
-}
{-
=α-symm : R.symmetric =α
=α-symm = ⋆symm ↝α-symm

=α-refl : R.reflexive =α
=α-refl = ⋆refl

=α-trans : R.transitive =α
=α-trans = _⋆trans_

=α-equiv : R.equivalence =α
=α-equiv = (=α-refl , =α-trans) , =α-symm

-}