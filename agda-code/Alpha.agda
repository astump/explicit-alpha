open import lib
open import relations as R
open import diamond
open import VarInterface

module Alpha(vi : VI) where

open VI vi
open import Tm vi
open import Ctxt vi
open import Beta vi
open import Apart vi
open import Subst vi
open import Tau vi

Renaming : Set
Renaming = 𝕃 (V × V)

renaming-dom : Renaming → 𝕃 V
renaming-dom = map fst

renaming-ran : Renaming → 𝕃 V
renaming-ran = map snd

data Lookup (x : V) : Renaming → V → Set where
  found : ∀{ρ : Renaming}{y : V} →
           Lookup x ((x , y) :: ρ) y
  next :  ∀{ρ : Renaming}{x' y y' : V} →
           Lookup x ρ y →
           x ≃ x' ≡ ff → 
           Lookup x ((x' , y') :: ρ) y

lookup : (x : V) → (ρ : Renaming) → maybe V
lookup x [] = nothing
lookup x ((x' , y) :: ρ) =
  if (x ≃ x') then just y
  else lookup x ρ 

InDom : V → Renaming → Set
InDom x ρ = Σ[ y ∈ V ] Lookup x ρ y

InRan : V → Renaming → Set
InRan x ρ = Σ[ y ∈ V ] Lookup y ρ x

InField : V → Renaming → Set
InField x ρ = InDom x ρ ∨ InRan x ρ

{- The Alpha relation ensures we do not identify bound variables, so we cannot
   block β-reductions when we take an Alpha-step -}
data Alpha : Renaming → Tm → Tm → Set where
 alphaMiss : ∀{ρ : Renaming}{x : V} →
               -- since the field of ρ is the set of variables bound in either term, we are saying x is not bound in either
               ¬ InField x ρ →
               Alpha ρ (var x) (var x)
 alphaHit : ∀{ρ : Renaming}{x y : V} →
              Lookup x ρ y →
              Alpha ρ (var x) (var y)
 alphaApp : ∀{ρ : Renaming}{t1 t1' t2 t2' : Tm} → 
              Alpha ρ t1 t1' →
              Alpha ρ t2 t2' →
              Alpha ρ (t1 · t2) (t1' · t2')
 alphaLam : ∀{ρ : Renaming}{x x' : V}{t t' : Tm} → 
              (∀ (y : V) → Lookup y ρ x' → x ≃ y ≡ tt) → -- the only variable that might be mapped to x' by ρ is x, so we cannot map two
                                                         -- different bound variables to x'.  So renaming can preserve but not increase
                                                         -- shadowing
              (x ≃ x' ≡ tt ∨ x' ∉ t) → -- we are either not doing a renaming here, or else we cannot capture a free x' in t
              Alpha ((x , x') :: ρ) t t' →
              Alpha ρ (ƛ x t) (ƛ x' t')

{-
1-1 : Renaming → Set
1-1 ρ = ∀{ρ1 ρ2 ρ3 : Renaming}{x x' y y' : V} →
         ρ ≡ ρ1 ++ (x , y) :: ρ2 ++ (x' , y') :: ρ3 →
         y ≡ y' →
         x ≡ x'

1-1-tail : ∀{ρ : Renaming}{y y' : V} →
           1-1 ((y , y') :: ρ) →
           1-1 ρ
1-1-tail{ρ}{z}{z'} oo {ρ1}{ρ2}{ρ3}{x}{y}{y'} eq = oo{ (z , z') :: ρ1}{ρ2}{ρ3} (cong (_::_ (z , z')) eq)

1-1-[] : 1-1 []
1-1-[]{[]} ()
1-1-[]{_ :: _} ()

-}

1-1 : Renaming → Set
1-1 ρ = ∀{ρ1 ρ2 : Renaming}{x x' y y' : V} →
         ρ ≡ ρ1 ++ ρ2 → 
         Lookup x ρ2 y →
         Lookup x' ρ2 y' →          
         y ≃ y' ≡ tt →
         x ≃ x' ≡ tt 

1-1-tail : ∀{ρ : Renaming}{z z' : V} →
           1-1 ((z , z') :: ρ) →
           1-1 ρ
1-1-tail{ρ}{z}{z'} oo {ρ1}{ρ2}{x}{x'} e1 L L' e2 = oo {(z , z') :: ρ1} {ρ2} (cong (_::_ (z , z')) e1) L L' e2

1-1-[] : 1-1 []
1-1-[] {[]} {[]} _ ()
1-1-[] {[]} {x :: ρ2} ()
1-1-[] {x :: ρ1} {[]} ()
1-1-[] {x :: ρ1} {x₁ :: ρ2} ()

freshen-var : Renaming → V → V
freshen-var ρ x with lookup x ρ
freshen-var ρ x | nothing = x
freshen-var ρ x | just y = y

freshenh : Renaming → Tm → Tm
freshenh ρ (var x) = var (freshen-var ρ x) 
freshenh ρ (t1 · t2) = freshenh ρ t1 · freshenh ρ t2 
freshenh ρ (ƛ x t) =
  let n = fresh (renaming-ran ρ) in
    ƛ n (freshenh ((x , n) :: ρ) t)

freshen : Tm → Tm
freshen t = freshenh [] t

-- return a new 1-1 renaming mapping either the domain (if given 𝔹 is tt) or range of the
-- given renaming to variables apart from the given list of variables
freshen-renaming : 𝔹 → 𝕃 V → Renaming → Renaming
freshen-renaming _ _ [] = []
freshen-renaming b ns ((x , y) :: ρ) =
  let n = fresh ns in
    ((if b then x else y) , n) :: freshen-renaming b (n :: ns) ρ

InDom-freshen-renaming : ∀{ρ : Renaming}{x : V}{ns : 𝕃 V} →
                          InDom x (freshen-renaming tt ns ρ) →
                          InDom x ρ
InDom-freshen-renaming {[]} (_ , ())
InDom-freshen-renaming {(y , y') :: ρ} (_ , found) = y' , found
InDom-freshen-renaming {(y , y') :: ρ} (x' , next f x) with InDom-freshen-renaming{ρ} (x' , f) 
InDom-freshen-renaming {(y , y') :: ρ} (x' , next f x) | c , l = c , next l x

Lookup-decomp : ∀{x y : V}{ρ : Renaming} →
                 Lookup x ρ y →
                 Σ[ ρ1 ∈ Renaming ]
                 Σ[ ρ2 ∈ Renaming ]
                 ρ ≡ ρ1 ++ (x , y) :: ρ2
Lookup-decomp{ρ = (x , y) :: ρ} found = [] , ρ , refl
Lookup-decomp (next l ne) with Lookup-decomp l 
Lookup-decomp{ρ = (x' , y') :: ρ} (next l ne) | ρ1 , ρ2 , e rewrite e = (x' , y') :: ρ1 , ρ2 , refl

Lookup-cons-1-1 : ∀{x' x y y' : V}{ρ : Renaming} →
                   1-1 ((y , y') :: ρ) →
                   Lookup x' ρ x →
--                   x ≃ y' ≡ ff → 
                   Lookup x' ((y , y') :: ρ) x
Lookup-cons-1-1{x'}{x}{y}{y'}{(x' , x) :: ρ} oo found with keep (x' ≃ y)
Lookup-cons-1-1{x'}{x}{y}{y'}{(x' , x) :: ρ} oo found | tt , p rewrite ≃-≡ p = {!found!}
Lookup-cons-1-1{x'}{x}{y}{y'}{(x' , x) :: ρ} oo found | ff , p = {!!}
Lookup-cons-1-1{x'}{x}{y}{y'}{(z , z') :: ρ} oo (next L ne) = {!!}


Lookup-1-1 : ∀{x y z z' : V}{ρ : Renaming} →
             1-1 ρ →
             Lookup x ρ y →
             Lookup x ((z , z') :: ρ) y →
             x ≃ z ≡ ff →
             y ≃ z' ≡ ff
Lookup-1-1 oo found L' ne = {!!}
Lookup-1-1 oo (next L x) L' ne = {!!}


InDomRan-freshen-renaming : ∀{ρ : Renaming}{x : V}{ns : 𝕃 V} →
                            1-1 ρ → 
                            InDom x (freshen-renaming ff ns ρ) → 
                            InRan x ρ
InDomRan-freshen-renaming{[]} oo (_ , ())
InDomRan-freshen-renaming {(y , y') :: ρ} oo (_ , found) = y , found
InDomRan-freshen-renaming{(y , y') :: ρ}{x} oo (a , next l ne) with InDomRan-freshen-renaming{ρ} (1-1-tail oo) (a , l) 
InDomRan-freshen-renaming{(y , y') :: ρ}{x} oo (_ , next l ne) | x' , L = x' , {!!} 

InRan-freshen-renaming : ∀{ρ : Renaming}{x : V}{ns : 𝕃 V}{b : 𝔹} →
                          list-member _≃_ x ns ≡ tt → 
                          ¬ InRan x (freshen-renaming b ns ρ) 
InRan-freshen-renaming{[]} _ (_ , ()) 
InRan-freshen-renaming {(y , y') :: ρ}{x}{ns} m (_ , found) rewrite fresh-distinct{ns} with m 
InRan-freshen-renaming {(y , y') :: ρ}{x}{ns} m (_ , found) | ()
InRan-freshen-renaming {(y , y') :: ρ}{x}{ns} m (c , next r ne) = InRan-freshen-renaming {ρ} (||-intro2{x ≃ fresh ns} m) (c , r)

freshen-diff-var : ∀{x z z' : V}{ρ : Renaming} →
                    x ≃ z ≡ ff → 
                    freshen-var ((z , z') :: ρ) x ≡ freshen-var ρ x
freshen-diff-var{x}{ρ = ρ} ne rewrite ne with lookup x ρ 
freshen-diff-var ne | nothing = refl
freshen-diff-var ne | just x' = refl

Lookup-freshen : ∀{x y : V}{ρ : Renaming}{ys : 𝕃 V} →
                 1-1 ρ → 
                 Lookup x ρ y →
                 let ρ' b = freshen-renaming b ys ρ in
                 Lookup y (ρ' ff) (freshen-var (ρ' tt) x)
Lookup-freshen {x} {y} {(x , y) :: ρ} _ found rewrite ≃-refl{x} = found
Lookup-freshen {x} {y} {(z , z') :: ρ}{ys} oo (next L ne) rewrite freshen-diff-var{x}{z}{fresh ys}{freshen-renaming tt (fresh ys :: ys) ρ} ne
  with Lookup-freshen{x}{y}{ρ}{fresh ys :: ys} (1-1-tail oo) L
Lookup-freshen {x} {y} {(z , z') :: ρ}{ys} oo (next L ne) | q = next q {!!} --(Lookup-1-1 (1-1-tail oo) L (next L ne) ne)

{-
found with keep (x ≃ x) 
Lookup-freshen{x}{y}{(x , y) :: ρ} found with keep (x ≃ x) 
Lookup-freshen{x}{y}{(x , y) :: ρ} found | tt , p rewrite ≃-≡ p = found
Lookup-freshen{x}{y}{(x , y) :: ρ} found | ff , p with ≃-refl{x} 
Lookup-freshen{x}{y}{(x , y) :: ρ} found | ff , p | q with trans (sym p) q 
Lookup-freshen{x}{y}{(x , y) :: ρ} found | ff , p | q | ()
Lookup-freshen{x}{y} (next{x' = x'}{y}{y'} L ne) with keep (x ≃ x') 
Lookup-freshen{x}{y} (next{x' = x'}{y}{y'} L ne) | tt , p with ≃-≡ p 
Lookup-freshen{x}{y} (next{x' = x'}{y}{y'} L ne) | tt , p | refl = {!!}
Lookup-freshen{x}{y} (next{x' = x'}{y}{y'} L ne) | ff , p = {!!}
-}
triangle-Alphah : ∀{ρ : Renaming} →
                    1-1 ρ →
                    {t t' : Tm} → 
                    Alpha ρ t t' →
                    let ρ' b = freshen-renaming b (fvs t') ρ in
                    Alpha (ρ' ff) t' (freshenh (ρ' tt) t)
triangle-Alphah {ρ} oo (alphaMiss {x = x} i) with lookup x (freshen-renaming tt [ x ] ρ)
triangle-Alphah {ρ} oo (alphaMiss {x = x} i) | nothing = alphaMiss h
  where h : ¬ InField x (freshen-renaming ff [ x ] ρ)
        h (inj₁ p) = i (inj₂ (InDomRan-freshen-renaming oo p))
        h (inj₂ p) = InRan-freshen-renaming (||-intro1{x ≃ x} (≃-refl{x})) p
triangle-Alphah {ρ} oo (alphaMiss {x} i) | just y = {!!}

triangle-Alphah {ρ} oo (alphaHit{x = x}{y} L) = alphaHit (Lookup-freshen oo L) 
triangle-Alphah {ρ} oo (alphaApp a a₁) = alphaApp {!!} {!!}
triangle-Alphah {ρ} oo (alphaLam x x₁ a) = alphaLam {!!} {!!} {!!}


triangle-Alpha : triangle freshen (Alpha [])
triangle-Alpha a = triangle-Alphah{[]} 1-1-[] a 

diamond-Alpha : diamond (Alpha [])
diamond-Alpha = triangle-diamond{f = freshen}{r = Alpha []} triangle-Alpha