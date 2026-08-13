open import lib hiding (_∘_)
open import VarInterface

module Substitution where

open import Tm
open import Apart

Substitution : Set
Substitution = 𝕃 (V × Tm)
infix 6 [_/_]_
[_/_]_ : Tm → V → Substitution → Substitution
[ t / v ] σ = (v , t) :: σ

lookup : Substitution → V → maybe Tm
lookup [] x = nothing
lookup ((y , t) :: σ) x = if x ≃ y then just t else lookup σ x

infix 7 _\\_
_\\_ : Substitution → V → Substitution
[] \\ _ = []
((x , t) :: σ) \\ y = if x ≃ y then σ \\ y else (x , t) :: (σ \\ y)

subst-var : Substitution → V → Tm
subst-var σ x with lookup σ x 
subst-var σ x | nothing = var x
subst-var σ x | just t = t

var-mapped : V → Substitution → 𝔹
var-mapped _ [] = ff
var-mapped x ((y , t) :: σ) = x ≃ y || var-mapped x σ


lookup-nothing : ∀{σ : Substitution}{x : V} →
                  lookup σ x ≡ nothing →
                  subst-var σ x ≡ var x
lookup-nothing{σ}{x} e with (lookup σ x)
lookup-nothing {_} {_} e | nothing = refl

lookup-just : ∀{σ : Substitution}{x : V}{t : Tm} →
                  lookup σ x ≡ just t →
                  subst-var σ x ≡ t
lookup-just{σ}{x} e with lookup σ x
lookup-just {σ} {x} refl | just x₁ = refl

-- capture is allowed
graft : Substitution → Tm → Tm
graft σ (var x) = subst-var σ x
graft σ (t1 · t2) = graft σ t1 · graft σ t2
graft σ (ƛ x t) = ƛ x (graft (σ \\ x) t)

graft1 : Tm → V → Tm → Tm
graft1 t2 y t1 = graft [ y , t2 ] t1

subst-Apart : Substitution → 𝕃 V → 𝔹
subst-Apart σ Γ = list-all (λ p → Apart (snd p) Γ) σ

dom : Substitution → 𝕃 V
dom = map fst

Renaming : Set
Renaming = 𝕃 (V × V)

domr : Renaming → 𝕃 V 
domr = map fst

ranr : Renaming → 𝕃 V 
ranr = map snd

idempotentr : Renaming → 𝔹
idempotentr ρ = list-all (λ v → ~ list-member _≃_ v (ranr ρ)) (domr ρ)

↑ : Renaming → Substitution
↑ = map (λ p → fst p , var (snd p))

-- the free variables in the range are apart from the domain of the substitution
idempotent : Substitution → 𝔹
idempotent σ = subst-Apart σ (dom σ)

graft-[] : ∀{t : Tm} → graft [] t ≡ t
graft-[] {var x} = refl
graft-[] {t1 · t2} rewrite graft-[] {t1} | graft-[] {t2} = refl
graft-[] {ƛ x t} rewrite graft-[] {t} = refl

infixl 7 _∘_ 

-- composition of substitutions by grafting into the range of the first one
_∘_ : Substitution → Substitution → Substitution
[] ∘ σ' = []
((x , t) :: σ) ∘ σ' = (x , graft σ' t) :: σ ∘ σ'

lookup-∘-nothing : ∀{x : V}{σ σ' : Substitution} →
                    lookup σ x ≡ nothing →
                    lookup (σ ∘ σ') x ≡ nothing 
lookup-∘-nothing {x} {[]} {σ'} eq = refl
lookup-∘-nothing {x} {(y , t) :: σ} {σ'} eq with x ≃ y 
lookup-∘-nothing {x} {(y , t) :: σ} {σ'} () | tt
lookup-∘-nothing {x} {(y , t) :: σ} {σ'} eq | ff rewrite lookup-∘-nothing{x}{σ}{σ'} eq = refl

lookup-∘-just : ∀{x : V}{σ σ' : Substitution}{t : Tm} →
                 lookup σ x ≡ just t →
                 lookup (σ ∘ σ') x ≡ just (graft σ' t) 
lookup-∘-just {x} {(y , t) :: σ} {σ'} {t'} eq with x ≃ y 
lookup-∘-just {x} {(y , t) :: σ} {σ'} {t'} refl | tt = refl
lookup-∘-just {x} {(y , t) :: σ} {σ'} {t'} eq | ff rewrite lookup-∘-just{x}{σ}{σ'}{t'} eq = refl

in-dom : V → Substitution → 𝔹
in-dom x σ = list-member _≃_ x (dom σ)   

lookup-mem : ∀{x : V}{σ : Substitution} →
              in-dom x σ ≡ tt →
              ∃ Tm λ r → lookup σ x ≡ just r
lookup-mem {x} {(y , r) :: σ} eq with x ≃ y 
lookup-mem {x} {(y , r) :: σ} eq | tt = r , refl
lookup-mem {x} {(y , r) :: σ} eq | ff = lookup-mem{x}{σ} eq

lookup-not-member : ∀{x : V}{σ : Substitution} →
                    list-member _≃_ x (dom σ) ≡ ff → 
                    lookup σ x ≡ nothing
lookup-not-member {x} {[]} sl = refl
lookup-not-member {x} {(y , _) :: σ} sl with x ≃ y 
lookup-not-member {x} {(y , _) :: σ} () | tt
lookup-not-member {x} {(y , _) :: σ} sl | ff = lookup-not-member{x}{σ} sl

subst-var-not-member : ∀{x : V}{σ : Substitution} →
                       list-member _≃_ x (dom σ) ≡ ff → 
                       subst-var σ x ≡ var x
subst-var-not-member{x}{σ} sl = lookup-nothing{σ} (lookup-not-member{x}{σ} sl)

graft-~∈ : ∀{x : V}{t t' : Tm} →
             x ∈ t' ≡ ff → 
             graft ((x , t) :: []) t' ≡ t'
graft-~∈ {x} {t} {var y} eq rewrite ~≃-sym{x} eq = refl
graft-~∈ {x} {t} {t' · t''} eq rewrite graft-~∈{x}{t}{t'} (fst (||-ff-elim{x ∈ t'} eq))
                                     | graft-~∈{x}{t}{t''} (snd (||-ff-elim{x ∈ t'} eq)) = refl
graft-~∈ {x} {t} {ƛ y t'} eq with &&-ff-elim{~ x ≃ y} eq
graft-~∈ {x} {t} {ƛ y t'} eq | inj₁ i rewrite ~ff-≡{x ≃ y} i | graft-[]{t'} = refl
graft-~∈ {x} {t} {ƛ y t'} eq | inj₂ i with keep (x ≃ y)
graft-~∈ {x} {t} {ƛ y t'} eq | inj₂ i | tt , eq' rewrite eq' | graft-[]{t'} = refl
graft-~∈ {x} {t} {ƛ y t'} eq | inj₂ i | ff , eq' rewrite eq' | graft-~∈{x}{t}{t'} i = refl