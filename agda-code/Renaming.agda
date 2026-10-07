open import lib
open import relations as R
open import diamond
open import VarInterface
open import functions

module Renaming(vi : VI) where

open VI vi 
open import Tm vi
open import VarOps vi

Renaming : Set
Renaming = 𝕃 (V × V)

-- we would like to define these with map, but then I am running into
-- what look like bugs in Agda where eta-expansions of fst are not equal to fst.
domr : Renaming → 𝕃 V
domr [] = []
domr ((x , y) :: ρ) = x :: domr ρ

ranr : Renaming → 𝕃 V
ranr [] = []
ranr ((x , y) :: ρ) = y :: ranr ρ

injectiver : Renaming → 𝔹
injectiver [] = tt
injectiver ((x , y) :: ρ) = ~ varmem y (ranr ρ) && injectiver ρ

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

rename : Renaming → V → V
rename r v with lookupr r v
rename r v | nothing = v
rename r v | just v' = v'

infix 7 _\\_
_\\_ : Renaming → V → Renaming
ρ \\ x = (x , x) :: ρ

applyr : Renaming → Tm → Tm
applyr ρ (var x) = var (rename ρ x)
applyr ρ (t1 · t2) = applyr ρ t1 · applyr ρ t2
applyr ρ (ƛ x t) = ƛ x (applyr (ρ \\ x) t)

infixr 10 _∙_ 

_∙_ : Renaming → Renaming → Renaming
ρ ∙ [] = []
ρ ∙ ((x , y) :: ρ') = (x , rename ρ y) :: ρ ∙ ρ'

domrs : ∀{n : ℕ} → 𝕍 Renaming n → 𝕍 (𝕃 V) n 
domrs ρs = map𝕍 domr ρs

ranrs : ∀{n : ℕ} → 𝕍 Renaming n → 𝕍 (𝕃 V) n 
ranrs ρs = map𝕍 ranr ρs
