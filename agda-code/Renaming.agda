open import lib
open import relations as R
open import diamond
open import VarInterface

module Renaming where

open import Tm 

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
ρ \\ x = (x , x) :: ρ

applyr : Renaming → Tm → Tm
applyr ρ (var x) = var (rename ρ x)
applyr ρ (t1 · t2) = applyr ρ t1 · applyr ρ t2
applyr ρ (ƛ x t) = ƛ x (applyr (ρ \\ x) t)

infixr 10 _∙_ 

_∙_ : Renaming → Renaming → Renaming
ρ ∙ [] = []
ρ ∙ ((x , y) :: ρ') = (x , rename ρ y) :: ρ ∙ ρ'

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

varmem-lookupr-ff : ∀{x y z : V}{ρ : Renaming} →
                    ~ varmem y (ranr ρ) ≡ tt →
                    lookupr ρ x ≡ just z →
                    z ≢ y
varmem-lookupr-ff {x} {y} {z} {(u , v) :: ρ} m l d with x ≃ u 
varmem-lookupr-ff {x} {y} {z} {(u , v) :: ρ} m refl d | tt with keep (y ≃ z)
varmem-lookupr-ff {x} {y} {z} {(u , v) :: ρ} m refl d | tt | tt , eq rewrite eq with m
varmem-lookupr-ff {x} {y} {z} {(u , v) :: ρ} m refl d | tt | tt , eq | ()
varmem-lookupr-ff {x} {y} {z} {(u , v) :: ρ} m refl refl | tt | ff , eq rewrite ≃-refl{y} with eq
varmem-lookupr-ff {x} {y} {z} {(u , v) :: ρ} m refl refl | tt | ff , eq | ()
varmem-lookupr-ff {x} {y} {z} {(u , v) :: ρ} m l d | ff = varmem-lookupr-ff {x} {y} {z}{ρ} (~||-elim2 {y ≃ v} m) l d

-- need to break out a lemma about lookupr for this one:
varmem-rename-ff : ∀{x y : V}{ρ : Renaming} →
                   ~ varmem y (ranr ρ) ≡ tt →
                   y ≃ x ≡ ff →
                   y ≃ (rename ρ x) ≡ ff 
varmem-rename-ff {x} {y} {[]} nmem neq = neq
varmem-rename-ff {x} {y} {(u , v) :: ρ} nmem neq with keep (x ≃ u) 
varmem-rename-ff {x} {y} {(u , v) :: ρ} nmem neq | tt , eq
 rewrite eq | fst (||-≡-ff{y ≃ v} (~-≡-tt{y ≃ v || varmem y (ranr ρ)} nmem)) = refl
varmem-rename-ff {x} {y} {(u , v) :: ρ} nmem neq | ff , eq with keep (lookupr ρ x) 
varmem-rename-ff {x} {y} {(u , v) :: ρ} nmem neq | ff , eq | nothing , eq' rewrite eq | eq' = neq
varmem-rename-ff {x} {y} {(u , v) :: ρ} nmem neq | ff , eq | just r , eq' rewrite eq | eq' with keep (y ≃ r)
varmem-rename-ff {x} {y} {(u , v) :: ρ} nmem neq | ff , eq | just r , eq' | ff , q = q
varmem-rename-ff {x} {y} {(u , v) :: ρ} nmem neq | ff , eq | just r , eq' | tt , q
 with varmem-lookupr-ff{x}{y}{r}{ρ} (~||-elim2{y ≃ v} nmem) eq' (sym (≃-≡{y} q))
varmem-rename-ff {x} {y} {(u , v) :: ρ} nmem neq | ff , eq | just r , eq' | tt , q | ()

lookupr-diag : ∀{x : V}{vs : 𝕃 V} → 
              varmem x vs ≡ tt → 
              lookupr (diagonal vs) x ≡ just x
lookupr-diag {x} {y :: vs} m with keep (x ≃ y)
lookupr-diag {x} {y :: vs} m | tt , eq rewrite eq | ≃-≡{x} eq = refl
lookupr-diag {x} {y :: vs} m | ff , eq rewrite eq = lookupr-diag{x}{vs} m

rename-diag : ∀{x : V}{vs : 𝕃 V} → 
              varmem x vs ≡ tt → 
              rename (diagonal vs) x ≡ x
rename-diag{x}{vs} m rewrite lookupr-diag{x}{vs} m = refl

ranr-diag : ∀{vs : 𝕃 V} → ranr (diagonal vs) ≡ vs
ranr-diag {[]} = refl
ranr-diag {x :: vs} rewrite ranr-diag{vs} = refl

domr-diag : ∀{vs : 𝕃 V} → domr (diagonal vs) ≡ vs
domr-diag {[]} = refl
domr-diag {x :: vs} rewrite domr-diag{vs} = refl

∙-ranr-ff : ∀{x y : V}{ρ : Renaming} →
            varmem x (ranr ρ) ≡ ff →
            [ x , y ] ∙ ρ ≡ ρ 
∙-ranr-ff {x} {y} {[]} nr = refl
∙-ranr-ff {x} {y} {(u , v) :: ρ} nr
 rewrite ~≃-sym{x} (fst (||-≡-ff{x ≃ v} nr)) | ∙-ranr-ff{x}{y}{ρ} (snd (||-≡-ff{x ≃ v} nr))= refl 

∙-\\ : ∀{x y : V}{ρ : Renaming} →
       varmem x (ranr ρ) ≡ ff →
       [ x , y ] ∙ ((y , x) :: ρ) ≡ ρ \\ y
∙-\\ {x} {y} {[]} ap with keep (x ≃ y) 
∙-\\ {x} {y} {[]} ap | tt , eq rewrite ≃-≡{x} eq | ≃-refl{y} = refl
∙-\\ {x} {y} {[]} ap | ff , eq rewrite ≃-refl{x} = refl
∙-\\ {x} {y} {(u , v) :: ρ} ap rewrite ≃-refl{x} | ~≃-sym{x} (fst (||-≡-ff{x ≃ v} ap))
                                     | ∙-ranr-ff{x}{y}{ρ} (snd (||-≡-ff{x ≃ v} ap)) = refl

applyr-∈ : ∀{y : V}{ρ : Renaming}{t : Tm} →
           ~ varmem y (ranr ρ) ≡ tt → 
           y ∈ t ≡ ff →
           y ∈ (applyr ρ t) ≡ ff 
applyr-∈ {y} {ρ} {var x} m n rewrite varmem-rename-ff{x}{y}{ρ} m (fst (||-ff-elim{y ≃ x} n)) = refl
applyr-∈ {y} {ρ} {t1 · t2} m n rewrite varmem-++ y (fvs (applyr ρ t1)) (fvs (applyr ρ t2))
                                     | varmem-++ y (fvs t1) (fvs t2)
                                     | applyr-∈{y}{ρ}{t1} m (fst (||-ff-elim{varmem y (fvs t1)} n))
                                     | applyr-∈{y}{ρ}{t2} m (snd (||-ff-elim{varmem y (fvs t1)} n)) = refl
applyr-∈ {y} {ρ} {ƛ x t} m n with varmem-remove2a{y}{x}{fvs t} n
applyr-∈ {y} {ρ} {ƛ x t} m n | inj₁ u rewrite ≃-≡{y} u = varmem-remove-same{x}{fvs (applyr (ρ \\ x) t)} 
applyr-∈ {y} {ρ} {ƛ x t} m n | inj₂ (u1 , u2) = 
 varmem-remove4 {y} {x} {fvs (applyr (ρ \\ x) t)} u1 (applyr-∈{y}{ρ \\ x}{t} h u2)
 where h : ~ varmem y (x :: ranr ρ) ≡ tt
       h rewrite u1 = m
