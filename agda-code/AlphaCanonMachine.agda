open import lib hiding (_>>=_ ; return ; _∘_)
open import functions
open import VarInterface

module AlphaCanonMachine where

open import Tm 
open import Renaming

Renamed = Tm

αb : Tm → Renaming → 𝕃 V → (Renamed → 𝕃 V → Renamed) → Renamed
αb (var x) ρ vs k = k (var (rename ρ x)) vs
αb (t1 · t2) ρ vs k = αb t1 ρ vs (λ r1 vs' → αb t2 ρ vs' (λ r2 vs' → k (r1 · r2) vs'))
αb (ƛ x t) ρ vs k =
  let n = fresh vs in
    αb t ((x , n) :: ρ) (n :: vs) (λ r vs' → ƛ n r)

{-
αb-app : ∀{t1 t2 : Tm}{vs : 𝕃 V}{k : Renamed → 𝕃 V → Renamed} →
         αb t1 vs k ≡ t1' ∧
         αb t2 vs' 
         αb (t1 · t2) vs k ≡ t1' · t2'
-}