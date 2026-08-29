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
triangle-⇒αβ = {!!}
