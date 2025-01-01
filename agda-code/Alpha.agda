{-# OPTIONS --allow-unsolved-metas #-}
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

lookup : Renaming → V → maybe V
lookup [] x = nothing
lookup ((x' , y) :: ρ) x =
  if (x ≃ x') then just y
  else lookup ρ x 

_/_ : Renaming → V → V
ρ / x with lookup ρ x 
ρ / x | nothing = x
ρ / x | just y = y

1-1-mapping : V → V → V × V → Set
1-1-mapping x y (x' , y') = x ≃ x' ≡ tt ∨ (x ≃ x' ≡ ff ∧ y ≃ y' ≡ ff)

1-1 : Renaming → V → V → Set
1-1 ρ x y = all-pred (1-1-mapping x y) ρ

mapping-apart : V → V × V → Set
mapping-apart x (y , z) = x ≃ z ≡ ff 

-- ρ does not map any variable to x, except it is allowed to map x to x
range-apart : V → Renaming → Set
range-apart x = all-pred (mapping-apart x)


{- proposal:

   - move oo argument from alphaHit to alphaLam
   - maybe add constraint to alphaLam that x' is not free in t, and drop the range-apart constraint from alphaMiss?

-}

{- The Alpha relation ensures we do not identify bound variables, so we cannot
   block β-reductions when we take an Alpha-step -}
data Alpha : Renaming → Tm → Tm → Set where
 alphaHit : ∀{ρ : Renaming}{x y : V} →
             (e : lookup ρ x ≡ just y) →  
             (oo : 1-1 ρ x y) →
             Alpha ρ (var x) (var y)
 alphaMiss : ∀{ρ : Renaming}{x : V} →
             (e : lookup ρ x ≡ nothing) →  
             (ra : range-apart x ρ) →
             Alpha ρ (var x) (var x)
 alphaApp : ∀{ρ : Renaming}{t1 t1' t2 t2' : Tm} → 
              Alpha ρ t1 t1' →
              Alpha ρ t2 t2' →
              Alpha ρ (t1 · t2) (t1' · t2')
 alphaLam : ∀{ρ : Renaming}{x x' : V}{t t' : Tm} → 
              Alpha ((x , x') :: ρ) t t' →
              Alpha ρ (ƛ x t) (ƛ x' t')

-- return a new 1-1 renaming mapping either the domain (if given 𝔹 is tt) or range of the
-- given renaming to variables apart from the given list of variables
freshen-renaming : 𝔹 → 𝕃 V → Renaming → Renaming 
freshen-renaming _ vs [] = [] 
freshen-renaming b vs ((x , y) :: ρ) =
  let ρ' = freshen-renaming b vs ρ in
  let n = fresh (renaming-ran ρ' ++ vs) in
    ((if b then x else y) , n) :: ρ' 

freshen-renaming-vars :  𝔹 → 𝕃 V → Renaming → 𝕃 V
freshen-renaming-vars b vs ρ = renaming-ran (freshen-renaming b vs ρ)

freshenh : 𝕃 V → Renaming → Tm → Tm
freshenh vs ρ (var x) = var (ρ / x) 
freshenh vs ρ (t1 · t2) = freshenh vs ρ t1 · freshenh vs ρ t2 
freshenh vs ρ (ƛ x t) =
  let n = fresh (renaming-ran ρ ++ vs) in
    ƛ n (freshenh vs ((x , n) :: ρ) t)

freshen : Tm → Tm
freshen t = freshenh (fvs t) [] t


{-

alphaVar-cons : ∀{ρ : Renaming}{y z' q w : V} →
                 y ≃ z' ≡ ff →
                 w ≃ q ≡ ff → 
                 Alpha ρ (var y) (var w) →
                 Alpha ((z' , q) :: ρ) (var y) (var w)
alphaVar-cons{ρ}{y}{z'}{q}{w} e1 e2 (alphaHit e' oo) = alphaHit h (inj₂ (e1 , e2) , oo)
 where h : if y ≃ z' then just q else lookup ρ y ≡ just w
       h rewrite e1 = e'
alphaVar-cons{ρ}{y}{z'}{q}{w} e1 e2 (alphaMiss e' ra) = alphaMiss h (e2 , ra)
 where h : if y ≃ z' then just q else lookup ρ y ≡ nothing 
       h rewrite e1 = e'

lookup-miss : ∀{ρ : Renaming}{x y q : V} → 
                y ≃ x ≡ ff → 
                (((x , q) :: ρ) / y) ≡ ρ / y 
lookup-miss{[]}{x}{y}{q} e rewrite e = refl
lookup-miss{(w , w') :: ρ}{x}{y}{q} e rewrite e = refl

1-1-freshen-renaming : ∀{ρ : Renaming}{x y : V}{vs : 𝕃 V} →
                        list-in y vs →
                        1-1 (freshen-renaming ff vs ρ) x y
1-1-freshen-renaming {[]} _ = triv
1-1-freshen-renaming {(z , z') :: ρ} {x} {y} {vs} I with keep (x ≃ z')
1-1-freshen-renaming {(z , z') :: ρ} {x} {y} {vs} I | tt , p = inj₁ p , {!!} -- 1-1-freshen-renaming I
1-1-freshen-renaming {(z , z') :: ρ} {x} {y} {vs} I | ff , p = inj₂ (p , ~≃-sym (fresh-distinct-in (list-in-++2 I))) , {!!} --1-1-freshen-renaming I

lookup-fresh : ∀{ρ : Renaming}{x y z : V}{vs : 𝕃 V} →
               lookup ρ x ≡ just y →
               list-in z vs → 
               (freshen-renaming tt vs ρ / x) ≃ z ≡ ff
lookup-fresh {(w , w') :: ρ} {x} {y} {z} {vs} L I with keep (x ≃ w) 
lookup-fresh {(w , w') :: ρ} {x} {y} {z} {vs} L I | tt , p rewrite p = fresh-distinct-in (list-in-++2 I) -- 
lookup-fresh {(w , w') :: ρ} {x} {y} {z} {vs} L I | ff , p rewrite p with lookup-fresh{ρ}{x}{y}{z}{fresh vs :: vs} L (inj₂ I)
lookup-fresh {(w , w') :: ρ} {x} {y} {z} {vs} L I | ff , p | q = {!!}

alphaVar-renaming : ∀{ρ : Renaming}{x y : V}{vs : 𝕃 V} →
                    lookup ρ x ≡ just y → 
                    1-1 ρ x y →
                    list-in y vs → 
                    Alpha
                      (freshen-renaming ff vs ρ)
                      (var y)
                      (var (freshen-renaming tt vs ρ / x))
alphaVar-renaming {(z , z') :: ρ} {x} {y} {vs} e (inj₁ p , oo) I rewrite p with e 
alphaVar-renaming {(z , z') :: ρ} {x} {y} {vs} e (inj₁ p , oo) I | refl =
  alphaHit {!!} {!!}
    {- (inj₁ (≃-refl{z'}) , 1-1-freshen-renaming {ρ} {z'}
                                    {fresh (renaming-ran (freshen-renaming tt vs ρ) ++ vs)} {!!}) -} 
  where h : ∀{b : maybe V} →
            (if z' ≃ z' then just (fresh ((renaming-ran (freshen-renaming ff vs ρ)) ++ vs)) else b) ≡
            just (fresh ((renaming-ran (freshen-renaming tt vs ρ)) ++ vs))
        h rewrite ≃-refl{z'} | freshen-renamings-ran{ρ}{vs} = refl

alphaVar-renaming {(z , z') :: ρ} {x} {y} {vs} e (inj₂ (p1 , p2) , oo) I
 rewrite lookup-miss{freshen-renaming tt (fresh vs :: vs) ρ}{z}{x}{fresh vs} p1 | p1
 with alphaVar-renaming{ρ}{x}{y}{fresh vs :: vs} e oo (inj₂ I) 
alphaVar-renaming {(z , z') :: ρ} {x} {y} {vs} e (inj₂ (p1 , p2) , oo) I | q = {!!}
  --alphaVar-cons p2 {!!} {-(lookup-fresh{ρ}{vs = fresh vs :: vs} e (inj₁ {!!}))-} {!!} --q

freshen-lookup-nothing : ∀{ρ : Renaming}{x : V}{vs : 𝕃 V} →
                          lookup ρ x ≡ nothing →
                          freshen-renaming tt vs ρ / x ≡ x
freshen-lookup-nothing {[]} L = refl
freshen-lookup-nothing {(y , y') :: ρ}{x} L with x ≃ y
freshen-lookup-nothing {(y , y') :: ρ}{x} L | tt with L
freshen-lookup-nothing {(y , y') :: ρ}{x} L | tt | ()
freshen-lookup-nothing {(y , y') :: ρ}{x} L | ff = {!!} -- freshen-lookup-nothing{ρ}{x} L

freshen-lookup-range-apart : ∀{ρ : Renaming}{x : V}{vs : 𝕃 V} →
                              range-apart x ρ →
                              lookup (freshen-renaming ff vs ρ) x ≡ nothing
freshen-lookup-range-apart {[]} A = refl
freshen-lookup-range-apart {(y , y') :: ρ} (p , A) rewrite p = {!!} -- freshen-lookup-range-apart A

range-apart-freshen : ∀{ρ : Renaming}{x : V}{vs : 𝕃 V}{b : 𝔹} →
                      list-in x vs →
                      range-apart x (freshen-renaming b vs ρ)
range-apart-freshen {[]} {x} {vs} {b} I = triv
range-apart-freshen {(y , y') :: ρ} {x} {vs} {b} I = {!!} -- ~≃-sym (fresh-distinct-in {!!}) , {!!} -- range-apart-freshen (inj₂ I)

-}

freshen-renamings-ran : ∀{ρ : Renaming}{vs : 𝕃 V} →
                        renaming-ran (freshen-renaming ff vs ρ) ≡ renaming-ran (freshen-renaming tt vs ρ)
freshen-renamings-ran {[]} = refl
freshen-renamings-ran {(x , y) :: ρ}{vs} rewrite freshen-renamings-ran{ρ}{vs} = refl

sublist-fvs-ƛ : ∀{x : V}{t : Tm}{vs : 𝕃 V} →
                sublist (fvs (ƛ x t)) vs →
                sublist (fvs t) (x :: vs)
sublist-fvs-ƛ = sublist-remove ≃-≡ ≃-refl

-- vs should be the free variables of t' not mapped by ρ
triangle-Alphah : ∀{ρ : Renaming} →
                    {t t' : Tm}{vs : 𝕃 V} →
                    sublist (fvs t) (renaming-dom ρ ++ vs) → 
                    Alpha ρ t t' →
                    let ρ' b = freshen-renaming b vs ρ in
                    Alpha (ρ' ff) t' (freshenh vs (ρ' tt) t)
triangle-Alphah {ρ} S (alphaHit {x = x}{y} e oo) = {!!} --alphaVar-renaming e oo (S (inj₁ refl))
triangle-Alphah {ρ}{vs = vs} S (alphaMiss {x = x} e RA) = {!!} {-rewrite freshen-lookup-nothing{ρ}{x}{vs} e =
  alphaMiss (freshen-lookup-range-apart RA) (range-apart-freshen (S (inj₁ refl)))  -}
triangle-Alphah {ρ} S (alphaApp a1 a2) = alphaApp (triangle-Alphah (sublist-++1 S) a1) (triangle-Alphah (sublist-++2 S) a2)
triangle-Alphah {ρ}{vs = vs} S (alphaLam{x = x}{x'}{t}{t'} a)
  with triangle-Alphah{(x , x') :: ρ}{t}{t'}{vs} (sublist-fvs-ƛ{x}{t} S) a 
triangle-Alphah {ρ}{vs = vs} S (alphaLam{x = x}{x'}{t}{t'} a) | B rewrite freshen-renamings-ran{ρ}{vs} = 
 alphaLam B 


triangle-Alpha : triangle freshen (Alpha [])
triangle-Alpha{t}{t'} a = triangle-Alphah{[]}{vs = fvs t} sublist-refl a 

diamond-Alpha : diamond (Alpha [])
diamond-Alpha = triangle-diamond{f = freshen}{r = Alpha []} triangle-Alpha

