open import lib
open import VarInterface

module Triangle where

open import Tm 
open import Subst
open import Apart
open import Rename
open import Renaming
open import AlphaCanon
open import Takahashi 
open import Parallel

triangle-⇒αβ : ∀{s t t' : Tm}{ρ : Renaming}{b : 𝔹} →
                s ⟨ ⇒αβ b ⟩ t →
                Rename ρ t t' → 
                t' ⟨ ⇒αβ ff ⟩ (αtk s ρ)
triangle-⇒αβ {var x} {t} {t'} {ρ} var var = {!!}
triangle-⇒αβ {var x · s} {var x · t} {var y · t'} {ρ} (app var d) (app var re) = {!!}
triangle-⇒αβ {s1 · s2 · s3} {t1 · t2} {t1' · t2'} {ρ} (app d1 d2) (app re1 re2) = {!!}

triangle-⇒αβ {(ƛ x s1) · s2} {(ƛ x' t1) · t2} {t1' · t2'} {ρ} (app (alpha nf df d1 sb) d2) (app (lam ca re1) re2) =
 {!!}
triangle-⇒αβ {ƛ x s1 · s2} {ƛ x t1 · t2} {(ƛ x t1') · t2'} {ρ} (app (lam d1) d2) (app (lam ca re1) re2) = {!!}
triangle-⇒αβ {(ƛ x s1) · s2} {t} {t'} {ρ} (beta d1 d2 sb) re = {!!}
triangle-⇒αβ {ƛ y s} {ƛ z t} {ƛ z t'} {ρ} (alpha nf df d sb) (lam ca re) = {!!}
triangle-⇒αβ {ƛ y s} {ƛ y t} {ƛ y t'} {ρ} (lam d) (lam ca re) = {!!}

