open import lib
open import VarInterface
open import functions

module Experiment where

open import Renaming
open import Tm

data TmList : ℕ → Set where
  $ : TmList 0
  var[_]_ : ∀{n : ℕ} → V → TmList n → TmList (suc n)
  ·_ : ∀{n : ℕ} → TmList (2 + n) → TmList (suc n)
  ƛ[_]_ : ∀{n : ℕ} → V → TmList (1 + n) → TmList (suc n)

infixr 10 var[_]_
infixr 9 ·_
infixr 8 ƛ[_]_

v0 = 0
v1 = 1

example : TmList 1
example = · (ƛ[ v1 ] var[ v1 ] (· var[ v0 ] var[ v0 ] $))

toTms : ∀{n : ℕ} → TmList n → 𝕍 Tm n
toTms $ = []
toTms (var[ x ] tl) = var x :: toTms tl
toTms (· tl) with toTms tl 
toTms (· tl) | t1 :: t2 :: ts = (t1 · t2) :: ts
toTms (ƛ[ x ] tl) with toTms tl
toTms (ƛ[ x ] tl) | t1 :: ts = (ƛ x t1) :: ts

fromTm : ∀{n : ℕ} → Tm → TmList n → TmList (suc n)
fromTm (var x) tl = var[ x ] tl
fromTm (t1 · t2) tl = · (fromTm t1 (fromTm t2 tl))
fromTm (ƛ x t) tl = ƛ[ x ] (fromTm t tl)

fromTms : ∀{n : ℕ} → 𝕍 Tm n → TmList n
fromTms [] = $
fromTms (t :: ts) = fromTm t (fromTms ts)

toFromTms : ∀{n : ℕ}{t : TmList n}{vs : 𝕍 Tm n} →
            toTms t ≡ vs → 
            fromTms vs ≡ t
toFromTms {zero} {$} {vs} refl = refl
toFromTms {suc n} {var[ x ] t} {v :: vs} u with ::𝕍-injective u 
toFromTms {suc n} {var[ x ] t} {v :: vs} u | refl , u2 rewrite toFromTms{n}{t}{vs} u2 = refl
toFromTms {suc n} {· t} {vs} u with keep (toTms t)
toFromTms {suc n} {· t} {vs} u | a :: b :: r , eq with toFromTms{suc (suc n)}{t}{a :: b :: r} eq
toFromTms {suc n} {· t} {vs} u | a :: b :: r , eq | uu rewrite eq | sym u | uu = refl
toFromTms {suc n} {ƛ[ x ] t} {vs} u with keep (toTms t) 
toFromTms {suc n} {ƛ[ x ] t} {vs} u | a :: r , eq with toFromTms{suc n}{t}{a :: r} eq 
toFromTms {suc n} {ƛ[ x ] t} {vs} u | a :: r , eq | uu rewrite eq | sym u | uu = refl

fromToTm : ∀{n : ℕ}{t : Tm}{tl : TmList n} →
            toTms (fromTm t tl) ≡ t :: (toTms tl)
fromToTm {n} {var x} {tl} = refl
fromToTm {n} {t1 · t2} {tl} rewrite fromToTm{suc n}{t1}{fromTm t2 tl} | fromToTm{n}{t2}{tl} = refl
fromToTm {n} {ƛ x t} {tl} rewrite fromToTm{n}{t}{tl} = refl

fromToTms : ∀{n : ℕ}{vs : 𝕍 Tm n} →
            toTms (fromTms vs) ≡ vs 
fromToTms {zero} {[]} = refl
fromToTms {suc n} {t :: vs} rewrite fromToTm{n}{t}{fromTms vs} | fromToTms{n}{vs} = refl

{---------------------------------------------------------------------
 αc{n} tl vs ρs

 This renames the n terms represented by the TmList tl.

 The list of variables vs grows across the whole computation
 (over all of tl), accumulating the fresh variables we have
 introduced.

 The vector ρs of renamings, one for each term in the TmList,
 is applied to the variables in those terms.
 ---------------------------------------------------------------------} 
αc : ∀{n : ℕ} → TmList n → 𝕃 V → 𝕍 Renaming n → TmList n
αc $ _ _ = $
αc (var[ x ] tl) vs (ρ :: ρs) = var[ rename ρ x ] (αc tl vs ρs)
αc (· tl) vs (ρ :: ρs) = · (αc tl vs (ρ :: ρ :: ρs))
αc (ƛ[ x ] tl) vs (ρ :: ρs) =
  let n = fresh vs in
    ƛ[ n ] (αc tl (n :: vs) (((x , n) :: ρ) :: ρs))

-- compute the set of free variables in each term in a given TmList.
fvsl : ∀{n : ℕ} → TmList n → 𝕍 (𝕃 V) n
fvsl $ = []
fvsl (var[ x ] t) = [ x ] :: fvsl t 
fvsl (· t) with fvsl t 
fvsl (· t) | f1 :: f2 :: fs = (f1 ++ f2) :: fs
fvsl (ƛ[ x ] t) with fvsl t 
fvsl (ƛ[ x ] t) | f1 :: fs = varrem x f1 :: fs

pathDistinct : ∀{n : ℕ} → 𝕍 (𝕃 V) n → TmList n → bool
pathDistinct vss $ = tt
pathDistinct (vs :: vss) (var[ x ] t) = varmem x vs && pathDistinct vss t
pathDistinct (vs :: vss) (· t) = pathDistinct (vs :: vs :: vss) t 
pathDistinct (vs :: vss) (ƛ[ x ] t) = ~ varmem x vs && pathDistinct ((x :: vs) :: vss) t 

bvsl : ∀{n : ℕ} → TmList n → 𝕃 V
bvsl $ = []
bvsl (var[ x ] t) = bvsl t
bvsl (· t) = bvsl t
bvsl (ƛ[ x ] t) = x :: bvsl t

allDistinct : ∀{n : ℕ} → 𝕍 (𝕃 V) n → TmList n → 𝔹
allDistinct vss t = pathDistinct vss t && varunique (bvsl t)

αc-pathDistinct : ∀{n : ℕ}{t : TmList n}{vs : 𝕃 V}{ρs : 𝕍 Renaming n} →
                   varsubs (ranrs ρs) (repeat𝕍 vs n) ≡ tt → 
                   varsubs (fvsl t) (domrs ρs) ≡ tt →
                   pathDistinct (ranrs ρs) (αc t vs ρs) ≡ tt
αc-pathDistinct {zero} {$} {vs} {[]} _ sub = refl
αc-pathDistinct {suc n} {var[ x ] t} {vs} {ρ :: ρs} rr sub
 = &&-intro {varmem (rename ρ x) (ranr ρ)} (varmem-rename {x} {ρ}
     (&&-elim1{varmem x (domr ρ)} (&&-elim1{varsub [ x ] (domr ρ)} sub)))
     (αc-pathDistinct {n} {t} {vs} {ρs} (&&-elim2 rr) (&&-elim2{varsub [ x ] (domr ρ)} sub))
αc-pathDistinct {suc n} {· t} {vs} {ρ :: ρs} rr sub with keep (fvsl t)
αc-pathDistinct {suc n} {· t} {vs} {ρ :: ρs} rr sub | f1 :: f2 :: fs , eq rewrite eq =
 αc-pathDistinct {suc (suc n)} {t} {vs} {ρ :: ρ :: ρs} h' h
 where h : varsubs (fvsl t) (domrs (ρ :: ρ :: ρs)) ≡ tt
       h rewrite eq | varsub-++{f1}{f2}{domr ρ} with (varsub f1 (domr ρ)) | (varsub f2 (domr ρ)) | varsubs fs (domrs ρs) 
       h | p1 | p2 | p3 rewrite &&-assoc p1 p2 p3 = sub
       h' : varsubs (ranrs (ρ :: ρ :: ρs)) (vs :: vs :: repeat𝕍 vs n) ≡ tt
       h' rewrite &&-elim1{varsub (ranr ρ) vs} rr = &&-elim2 rr
αc-pathDistinct {suc n} {ƛ[ x ] t} {vs} {ρ :: ρs} rr sub with keep (fvsl t) 
αc-pathDistinct {suc n} {ƛ[ x ] t} {vs} {ρ :: ρs} rr sub | f :: fs , eq rewrite eq = 
 let q = fresh vs in
  &&-intro {~ varmem q (ranr ρ)}
    (~-≡-ff {varmem q (ranr ρ)}
      (varmem-varsub-ff {q} {ranr ρ} {vs} (&&-elim1{varsub (ranr ρ) vs} rr) (fresh-distinct {vs})))
    (αc-pathDistinct{suc n}{t}{q :: vs}{((x , q) :: ρ) :: ρs} h' h)
 where h : varsubs (fvsl t) (domrs (((x , fresh-ℕ vs) :: ρ) :: ρs)) ≡ tt
       h rewrite eq = &&-intro {varsub f (x :: domr ρ)}
                        (varsub-remove {f} {domr ρ} {x} (&&-elim1 sub)) (&&-elim2 sub)
       h' : varsubs (ranrs (((x , fresh-ℕ vs) :: ρ) :: ρs))
                    ((fresh-ℕ vs :: vs) :: repeat𝕍 (fresh-ℕ vs :: vs) n)
             ≡ tt
       h' rewrite ≃-refl{fresh vs} =
         &&-intro {varsub (ranr ρ) (fresh vs :: vs)} (varsub-++2 {[ fresh vs ]} {ranr ρ} {vs} (&&-elim1 rr))
          (varsubs-++2 {n} {[ fresh vs ]} {ranrs ρs} {vs} (&&-elim2 rr))

αc-bvs-fresh : ∀{v : V}{n : ℕ}{t : TmList n}{vs1 vs2 : 𝕃 V}{ρs : 𝕍 Renaming n} →
               varmem v (bvsl (αc t (vs1 ++ v :: vs2) ρs)) ≡ ff
αc-bvs-fresh {v} {zero} {$} {vs1}{vs2} {ρs} = refl
αc-bvs-fresh {v} {suc n} {var[ x ] t} {vs1}{vs2} {ρ :: ρs} = αc-bvs-fresh {v} {n} {t} {vs1}{vs2} {ρs}
αc-bvs-fresh {v} {suc n} {· t} {vs1}{vs2}{ρ :: ρs} = αc-bvs-fresh {v} {suc (suc n)} {t} {vs1}{vs2} {ρ :: ρ :: ρs}
αc-bvs-fresh {v} {suc n} {ƛ[ x ] t} {vs1}{vs2} {ρ :: ρs} = h
 where h : v ≃ fresh (vs1 ++ v :: vs2)
        || varmem v (bvsl (αc t (fresh (vs1 ++ v :: vs2) :: vs1 ++ v :: vs2)
                          (((x , fresh (vs1 ++ v :: vs2)) :: ρ) :: ρs))) ≡ ff
       h rewrite fresh-extend-mem{v}{vs1}{vs2} =
         αc-bvs-fresh{v}{suc n}{t}{fresh (vs1 ++ v :: vs2) :: vs1}{vs2}{(((x , fresh (vs1 ++ v :: vs2)) :: ρ) :: ρs)}

αc-bvs-unique : ∀{n : ℕ}{t : TmList n}{vs : 𝕃 V}{ρs : 𝕍 Renaming n} →
                varunique (bvsl (αc t vs ρs)) ≡ tt 
αc-bvs-unique {zero} {$} {vs} {ρs} = refl
αc-bvs-unique {suc n} {var[ x ] t} {vs} {ρ :: ρs} = αc-bvs-unique{n}{t}{vs}{ρs}
αc-bvs-unique {suc n} {· t} {vs} {ρ :: ρs} = αc-bvs-unique{suc (suc n)}{t}{vs}{ρ :: ρ :: ρs}
αc-bvs-unique {suc n} {ƛ[ x ] t} {vs} {ρ :: ρs} = h
 where h : ~ varmem (fresh vs) (bvsl (αc t (fresh vs :: vs) (((x , fresh vs) :: ρ) :: ρs)))
           && varunique (bvsl (αc t (fresh vs :: vs) (((x , fresh vs) :: ρ) :: ρs))) ≡ tt
       h rewrite αc-bvs-unique{suc n}{t}{fresh vs :: vs}{(((x , fresh vs) :: ρ) :: ρs)}
               | αc-bvs-fresh{fresh vs}{suc n}{t}{[]}{vs}{(((x , fresh vs) :: ρ) :: ρs)} =
         refl

αc-allDistinct : ∀{n : ℕ}{t : TmList n}{vs : 𝕃 V}{ρs : 𝕍 Renaming n} →
                  varsubs (ranrs ρs) (repeat𝕍 vs n) ≡ tt → 
                  varsubs (fvsl t) (domrs ρs) ≡ tt →
                  allDistinct (ranrs ρs) (αc t vs ρs) ≡ tt
αc-allDistinct{n}{t}{vs}{ρs} rr sub rewrite αc-pathDistinct{n}{t}{vs}{ρs} rr sub =
 αc-bvs-unique{n}{t}{vs}{ρs}