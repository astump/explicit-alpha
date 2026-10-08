open import lib
open import VarInterface

module Lemmas.Apart(vi : VI) where

open VI vi

open import Tm vi
open import VarOps vi
open import Apart vi

Apart-++1 : ∀{t : Tm}{vs1 vs2 : 𝕃 V} →
            Apart t (vs1 ++ vs2) ≡ tt →
            Apart t vs1 ≡ tt 
Apart-++1{t}{vs1}{vs2} p rewrite list-all-append (λ v → ~ v ∈ t) vs1 vs2 = &&-elim1 p

Apart-++2 : ∀{t : Tm}{vs1 vs2 : 𝕃 V} →
            Apart t (vs1 ++ vs2) ≡ tt →
            Apart t vs2 ≡ tt
Apart-++2{t}{vs1}{vs2} p rewrite list-all-append (λ v → ~ v ∈ t) vs1 vs2 = &&-elim2 p
