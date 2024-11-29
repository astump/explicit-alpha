open import lib
open import relations as R
open import VarInterface

module Alpha(vi : VI) where

open VI vi
open import Tm vi
open import Ctxt vi
open import Beta vi
open import Apart vi
open import Subst vi
open import Tau vi

{- (ƛ x t1) and (ƛ y t1') are related by bare α iff

   1. y is not free in t1
   2. (safely) substituting y for x in t1 yields t1'
-}

α : Rel Tm
α (ƛ x t1) (ƛ y t1') = Apart t1 [ y ] ∧ Subst [] (var y) x t1 t1' 

α _ _ = ⊥

{- single-step α-reduction

   A single α-renaming is allowed anywhere in the first term to reach the second.
   But this renaming has to preserve β-reductions: any time the first term could
   β-reduce, the second term can, too, to an α-related result -}
↝α : Rel Tm
↝α t1 t2 =

  t1 ⟨ τ α ⟩ t2 ∧

  -- whenever t1 β-steps, so does t2; and the two resulting terms are related by τ α
  (∀ (t1' : Tm) →
      t1 ⟨ ↝β ⟩ t1' →
      Σ[ t2' ∈ Tm ]
         t2 ⟨ ↝β ⟩ t2' ∧
         t1' ⟨ τ α ⟩ t2') 

----------------------------------------------------------------------
-- Theorems about α
----------------------------------------------------------------------


{-
α-symm : R.symmetric α
α-symm {ƛ x t1} {ƛ y t1'} s = {!!}

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