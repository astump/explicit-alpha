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

invert : Renaming → Renaming
invert [] = []
invert ((x , y) :: ρ) = (y , x) :: invert ρ 

lookupr : Renaming → V → maybe V
lookupr [] x = nothing
lookupr ((x' , y) :: ρ) x =
  if (x ≃ x') then just y
  else lookupr ρ x 

definedr : Renaming → V → 𝔹
definedr ρ x = isJust (lookupr ρ x)

definedr-member : ∀{x : V}{ρ : Renaming} →
                  definedr ρ x ≡ tt →
                  varmem x (domr ρ) ≡ tt
definedr-member {x} {(x' , y) :: ρ} df with x ≃ x'
definedr-member {x} {(x' , y) :: ρ} df | tt = refl
definedr-member {x} {(x' , y) :: ρ} df | ff = definedr-member{x}{ρ} df

rename : Renaming → V → V
rename r v with lookupr r v
rename r v | nothing = v
rename r v | just v' = v'

infix 7 _\\_
_\\_ : Renaming → V → Renaming
[] \\ _ = []
((x , t) :: σ) \\ y = if x ≃ y then σ \\ y else (x , t) :: (σ \\ y)

varmem-renameh : ∀{x : V}{ρ : Renaming} →
                varmem x (domr ρ) ≡ tt →
                ∃ V (λ y → lookupr ρ x ≡ just y ∧ 
                           varmem y (ranr ρ) ≡ tt)
varmem-renameh {x} {(x' , y) :: ρ} vm with x ≃ x' 
varmem-renameh {x} {(x' , y) :: ρ} vm | tt = y , refl , ||-intro1{y ≃ y} (≃-refl{y})
varmem-renameh {x} {(x' , y) :: ρ} vm | ff with varmem-renameh {x} {ρ} vm 
varmem-renameh {x} {(x' , y) :: ρ} vm | ff | y' , l , m = y' , l , ||-intro2{y' ≃ y} m

varmem-rename : ∀{x : V}{ρ : Renaming} →
                varmem x (domr ρ) ≡ tt →
                varmem (rename ρ x) (ranr ρ) ≡ tt
varmem-rename{x}{ρ} mv with varmem-renameh{x}{ρ} mv 
varmem-rename{x}{ρ} mv | y , l , m rewrite l = m