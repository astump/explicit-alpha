-- define Alpha equivalence as a relation, parametrized by
-- a renaming for free variables

{-# OPTIONS --allow-unsolved-metas #-}
open import lib
open import VarInterface

module Alpha where

open import Tm 
open import Renaming
open import Subst

data Alpha : Renaming → Tm → Tm → Set where
  var : ∀{v v' : V}{ρ : Renaming} →
         lookupr ρ v ≡ just v' → 
         Alpha ρ (var v) (var v')
  app : ∀{t1 t2 t1' t2' : Tm}{ρ : Renaming} → 
         Alpha ρ t1 t1' →
         Alpha ρ t2 t2' →
         Alpha ρ (t1 · t2) (t1' · t2')
  lam : ∀{x y : V}{s s' : Tm}{ρ : Renaming} →
        varmem y (ranr ρ) ≡ ff →                 -- avoid capture
        x ≃ y ≡ ff → 
        Alpha ((x , y) :: ρ) s s' →
        Alpha ρ (ƛ x s) (ƛ y s')


{-
Alpha-trans : ∀{r s t : Tm}{ρ ρ' : Renaming} →
              Alpha ρ  r s →
              Alpha ρ' s t →
              Alpha (ρ' ∙ ρ) r t
Alpha-trans = {!!}              
-}