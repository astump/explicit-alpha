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
open import Vartree vi

Renaming : Set
Renaming = 𝕃 (V × V)

data Lookup (x : V) : Renaming → V → Set where
  found : ∀{ρ : Renaming}{y : V} →
           Lookup x ((x , y) :: ρ) y
  next :  ∀{ρ : Renaming}{x' y y' : V} →
           Lookup x ρ y →
           x ≃ x' ≡ ff → 
           Lookup x ((x' , y') :: ρ) y

data Rename : Renaming → Tm → Tm → Set where
 renameMiss : ∀{ρ : Renaming}{x : V} →
               (∀ (y : V) → ¬ Lookup x ρ y) →
               Rename ρ (var x) (var x)
 renameHit : ∀{ρ : Renaming}{x y : V} →
              Lookup x ρ y →
              Rename ρ (var x) (var y)
 renameApp : ∀{ρ : Renaming}{t1 t1' t2 t2' : Tm} → 
              Rename ρ t1 t1' →
              Rename ρ t2 t2' →
              Rename ρ (t1 · t2) (t1' · t2')
 renameLam : ∀{ρ : Renaming}{x x' : V}{t t' : Tm} → 
              Rename ((x , x') :: ρ) t t' →
              Rename ρ (ƛ x t) (ƛ x' t')

{- t1 alpha-reduces to t2 iff t1 can be renamed to t2 (with initially empty renaming),
   and all the bound variables of t2 are distinct.  The latter condition ensures that
   we do not block β-reductions when we take an ↝α-step -}
↝α : Rel Tm
↝α t1 t2 =
  DistinctBVs t2 ∧
  Rename [] t1 t2


⊥