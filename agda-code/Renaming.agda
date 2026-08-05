open import lib
open import relations as R
open import diamond
open import VarInterface

module Renaming where

open import Tm 

Renaming : Set
Renaming = 𝕃 (V × V)

domr : Renaming → 𝕃 V
domr [] = []
domr ((x , y) :: ρ) = x :: domr ρ

ranr : Renaming → 𝕃 V
ranr [] = []
ranr ((x , y) :: ρ) = y :: ranr ρ

lookupr : Renaming → V → maybe V
lookupr [] x = nothing
lookupr ((x' , y) :: ρ) x =
  if (x ≃ x') then just y
  else lookupr ρ x 

rename : Renaming → V → V
rename r v with lookupr r v
rename r v | nothing = v
rename r v | just v' = v'

domr-lookupr : ∀{x : V}{ρ : Renaming} →
            list-member _≃_ x (domr ρ) ≡ tt →
            isJust (lookupr ρ x) ≡ tt
domr-lookupr {x} {(y , z) :: ρ} mem with keep (x ≃ y)
domr-lookupr {x} {(y , z) :: ρ} mem | tt , eq rewrite eq = refl
domr-lookupr {x} {(y , z) :: ρ} mem | ff , eq rewrite eq = domr-lookupr{x}{ρ} mem

lookupr-ranr : ∀{x y : V}{ρ : Renaming} →
               lookupr ρ x ≡ just y → 
               list-member _≃_ y (ranr ρ) ≡ tt
lookupr-ranr {x} {y} {(x' , y') :: ρ} eq with x ≃ x'
lookupr-ranr {x} {y} {(x' , y') :: ρ} refl | tt rewrite ≃-refl{y} = refl
lookupr-ranr {x} {y} {(x' , y') :: ρ} eq | ff rewrite lookupr-ranr{x}{y}{ρ} eq = ||-tt (y ≃ y')

domr-ranr : ∀{x : V}{ρ : Renaming} →
            list-member _≃_ x (domr ρ) ≡ tt →
            list-member _≃_ (rename ρ x) (ranr ρ) ≡ tt
domr-ranr{x}{ρ} mem with domr-lookupr{x}{ρ} mem 
domr-ranr{x}{ρ} mem | eq with keep (lookupr ρ x) 
domr-ranr{x}{ρ} mem | eq | nothing , eq' rewrite eq' with eq
domr-ranr{x}{ρ} mem | eq | nothing , eq' | ()
domr-ranr{x}{ρ} mem | eq | just y , eq' rewrite eq' = lookupr-ranr{x}{y}{ρ} eq'