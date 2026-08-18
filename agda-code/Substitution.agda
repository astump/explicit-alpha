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
graft-~∈ {x} {t} {var y} eq rewrite ~≃-sym{x} (∈var{x}{y}{ff} eq) = refl -- rewrite ~≃-sym{x} eq = refl
graft-~∈ {x} {t} {t' · t''} eq rewrite graft-~∈{x}{t}{t'} (fst (∈·{x}{t'}{t''} eq))
                                     | graft-~∈{x}{t}{t''} (snd (∈·{x}{t'}{t''} eq)) = refl
graft-~∈ {x} {t} {ƛ y t'} eq with varmem-remove2{x}{y}{fvs t'} eq 
graft-~∈ {x} {t} {ƛ y t'} eq | inj₁ i rewrite i | graft-[]{t'} = refl
graft-~∈ {x} {t} {ƛ y t'} eq | inj₂ i with x ≃ y 
graft-~∈ {x} {t} {ƛ y t'} eq | inj₂ i | tt rewrite graft-[]{t'} = refl
graft-~∈ {x} {t} {ƛ y t'} eq | inj₂ i | ff rewrite graft-~∈{x}{t}{t'} i = refl

fvs-graft : ∀{x : V}{t1 t2 : Tm} →
               varsub (fvs (graft1 t2 x t1)) (varrem x (fvs t1) ++ fvs t2) ≡ tt
fvs-graft {x} {var y} {t} with keep (x ≃ y)
fvs-graft {x} {var y} {t} | tt , eq rewrite eq | ≃-sym{x} eq = isSublist-refl (λ{x} → ≃-refl{x}) {fvs t}
fvs-graft {x} {var y} {t} | ff , eq rewrite eq | ~≃-sym{x} eq | ≃-refl{y} = refl
fvs-graft {x} {t1 · t2} {t} = varsub-++il {fvs (graft [ x , t ] t1)}
                                  {fvs (graft [ x , t ] t2)}
                                  {varrem x (fvs t1 ++ fvs t2) ++ fvs t}
                                  (varsub-trans {fvs (graft [ x , t ] t1)}
                                    {varrem x (fvs t1) ++ fvs t}
                                    {varrem x (fvs t1 ++ fvs t2) ++ fvs t} 
                                    (fvs-graft{x}{t1}{t})
                                    (varsub-++-merge {varrem x (fvs t1)}
                                      {varrem x (fvs t1 ++ fvs t2)} {fvs t} {fvs t} 
                                      (varsub-trans  {varrem x (fvs t1)}
                                        {varrem x (fvs t1) ++ varrem x (fvs t2)}
                                        {varrem x (fvs t1 ++ fvs t2)} 
                                        (varsub-++1  {varrem x (fvs t1)}
                                           {varrem x (fvs t2)}) h)
                                           (varsub-refl {fvs t})))
                                  (varsub-trans {fvs (graft [ x , t ] t2)}
                                    {varrem x (fvs t2) ++ fvs t}
                                    {varrem x (fvs t1 ++ fvs t2) ++ fvs t}
                                    (fvs-graft {x} {t2} {t})
                                    ((varsub-++-merge {varrem x (fvs t2)}
                                      {varrem x (fvs t1 ++ fvs t2)} {fvs t} {fvs t} 
                                      (varsub-trans  {varrem x (fvs t2)}
                                        {varrem x (fvs t1) ++ varrem x (fvs t2)}
                                        {varrem x (fvs t1 ++ fvs t2)} 
                                        (varsub-++2a  {varrem x (fvs t1)}
                                           {varrem x (fvs t2)}) h)
                                           (varsub-refl {fvs t}))))
    where h : isSublist (varrem x (fvs t1) ++ varrem x (fvs t2))
                        (varrem x (fvs t1 ++ fvs t2)) _≃_
              ≡ tt
          h rewrite remove-++ _≃_ x (fvs t1) (fvs t2) | isSublist-refl{eq = _≃_} (λ{x} → ≃-refl{x})
                                                            {varrem x (fvs t1) ++ varrem x (fvs t2)} = refl
fvs-graft {x} {ƛ y t1} {t} with keep (x ≃ y)
fvs-graft {x} {ƛ y t1} {t} | tt , eq rewrite eq | graft-[] {t1} | ≃-≡{x} eq | remove-idem{eq = _≃_}{y}{fvs t1} = varsub-++1{varrem y (fvs t1)}
fvs-graft {x} {ƛ y t1} {t} | ff , eq rewrite eq  =
  varsub-trans {varrem y (fvs (graft1 t x t1))}{varrem y (varrem x (fvs t1) ++ fvs t)}{varrem x (varrem y (fvs t1)) ++ fvs t}
    (varsub-remove-both {fvs (graft1 t x t1)}
      {varrem x (fvs t1) ++ fvs t} {y} (fvs-graft{x}{t1}{t})) h
 where g : varsub (varrem y (varrem x (fvs t1)))
                  (varrem x (varrem y (fvs t1)))
            ≡ tt
       g rewrite varrem-commute{x}{y}{fvs t1} = varsub-refl{varrem y (varrem x (fvs t1))}
       h : varsub (varrem y (varrem x (fvs t1) ++ fvs t))
                  (varrem x (varrem y (fvs t1)) ++ fvs t)
            ≡ tt
       h rewrite varrem-++{varrem x (fvs t1)}{fvs t}{y} =
         varsub-++-merge {varrem y (varrem x (fvs t1))}
          {varrem x (varrem y (fvs t1))} {varrem y (fvs t)} {fvs t} g (varsub-remove2 {fvs t} {fvs t} {y} (varsub-refl{fvs t})) 

bvs-graft : ∀{x : V}{t1 t2 : Tm} →
            varsub (bvs (graft1 t2 x t1)) (bvs t1 ++ bvs t2) ≡ tt
bvs-graft {x} {var y} {t} with y ≃ x
bvs-graft {x} {var y} {t} | tt = varsub-refl{bvs t}
bvs-graft {x} {var y} {t} | ff = refl
bvs-graft {x} {t1 · t2} {t} = varsub-++il {bvs (graft1 t x t1)} {bvs (graft1 t x t2)}
                               {bvs (t1 · t2) ++ bvs t}
                               (varsub-trans {bvs (graft1 t x t1)} {bvs t1 ++ bvs t}
                                 {(bvs t1 ++ bvs t2) ++ bvs t}
                                 (bvs-graft{x}{t1}{t})
                                 (varsub-++-merge {bvs t1} {bvs t1 ++ bvs t2} {bvs t} {bvs t}
                                   (varsub-++1{bvs t1}{bvs t2})
                                   (varsub-refl{bvs t})))
                               (varsub-trans {bvs (graft1 t x t2)} {bvs t2 ++ bvs t}
                                 {(bvs t1 ++ bvs t2) ++ bvs t}
                                 (bvs-graft{x}{t2}{t})
                                 ((varsub-++-merge {bvs t2} {bvs t1 ++ bvs t2} {bvs t} {bvs t}
                                   (varsub-++2a{bvs t1}{bvs t2})
                                   (varsub-refl{bvs t}))))
bvs-graft {x} {ƛ y t1} {t} with x ≃ y 
bvs-graft {x} {ƛ y t1} {t} | tt rewrite ≃-refl{y} | graft-[]{t1} =
   list-all-sub {p = λ a → varmem a (bvs t1 ++ bvs t)}
                {q = λ a → (a ≃ y) || varmem a (bvs t1 ++ bvs t)}
                (bvs t1)
                (λ a → ||-intro2{a ≃ y})
                (varsub-++1{bvs t1}{bvs t}) 
bvs-graft {x} {ƛ y t1} {t} | ff rewrite ≃-refl{y} =
   list-all-sub {p = λ a → varmem a (bvs t1 ++ bvs t)}
                {q = λ a → (a ≃ y) || varmem a (bvs t1 ++ bvs t)}
                (bvs (graft1 t x t1))
                (λ a → ||-intro2{a ≃ y})
                (bvs-graft{x}{t1}{t})
