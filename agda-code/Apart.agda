open import lib
open import VarInterface

module Apart where

open import Tm

Apart : Tm → 𝕃 V → 𝔹
Apart t vs = varapart vs (fvs t) 

Apart-++1 : ∀{t : Tm}{vs1 vs2 : 𝕃 V} →
            Apart t (vs1 ++ vs2) ≡ tt →
            Apart t vs1 ≡ tt 
Apart-++1{t}{vs1}{vs2} p rewrite list-all-append (λ v → ~ v ∈ t) vs1 vs2 = &&-elim1 p

Apart-++2 : ∀{t : Tm}{vs1 vs2 : 𝕃 V} →
            Apart t (vs1 ++ vs2) ≡ tt →
            Apart t vs2 ≡ tt
Apart-++2{t}{vs1}{vs2} p rewrite list-all-append (λ v → ~ v ∈ t) vs1 vs2 = &&-elim2 p

