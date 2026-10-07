open import lib
open import bool-relations
open import VarInterface

module VarImpls where

----------------------------------------------------------------------
-- an implementation of the above interface based on V = ℕ

s+ : ℕ → ℕ → ℕ
s+ x y = suc (x + y)

VI-ℕ : VI
VI-ℕ = record {
        V = ℕ ;
        _≃_ = _=ℕ_ ;
        ≃-equivalence = =ℕ-equivalence ;
        ≃-≡ = =ℕ-to-≡ 
        }

-- open VI VI-ℕ public

----------------------------------------------------------------------
-- an implementation of the above interface based on V = 𝕃 𝔹
--
-- variables are bit strings, which makes it easier to choose distinct
-- variables in a term (see AlphaCanon.agda)

𝕃𝔹 = 𝕃 𝔹
_=𝕃𝔹_ = (=𝕃 _iff_)

=𝕃𝔹-equivalence : equivalence _=𝕃𝔹_
=𝕃𝔹-equivalence = =𝕃-equiv _iff_ iff-equiv
=𝕃𝔹-computational-equality = =𝕃-computational-equality _iff_ iff-computational-equality

VI-𝕃𝔹 : VI
VI-𝕃𝔹 = record {
        V = 𝕃𝔹 ;
        _≃_ = _=𝕃𝔹_ ;
        ≃-equivalence = =𝕃𝔹-equivalence ;
        ≃-≡ = =𝕃𝔹-computational-equality 

        }

