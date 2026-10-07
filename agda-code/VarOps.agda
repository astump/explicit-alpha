open import lib
open import bool-relations
open import functions
open import VarInterface

module VarOps(vi : VI) where

open VI vi 

varmem : V → 𝕃 V → 𝔹
varmem x vs = list-member _≃_ x vs

varsub : 𝕃 V → 𝕃 V → 𝔹
varsub vs vs' = isSublist vs vs' _≃_

varsubs : ∀{n : ℕ} → 𝕍 (𝕃 V) n → 𝕍 (𝕃 V) n → 𝔹
varsubs vss1 vss2 = 𝕍-all id (zipWith𝕍 varsub vss1 vss2) 

varapart : 𝕃 V → 𝕃 V → 𝔹
varapart vs vs' = disjoint _≃_ vs vs' 

varrem : V → 𝕃 V → 𝕃 V
varrem = remove _≃_

varunique : 𝕃 V → 𝔹
varunique = unique _≃_
