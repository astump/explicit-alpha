-- {-# OPTIONS --allow-unsolved-metas #-}

open import lib hiding (_>>=_ ; return ; _∘_)
open import VarInterface
open import VarImpls

module Lemmas.AlphaCanon where

open VI VI-𝕃𝔹

open import Tm VI-𝕃𝔹
open import VarOps VI-𝕃𝔹
open import Renaming VI-𝕃𝔹
open import Lemmas.Renaming VI-𝕃𝔹
open import Lemmas.VarOps VI-𝕃𝔹
open import Lemmas.VarInterface VI-𝕃𝔹
open import Lemmas.Fresh 
open import AlphaCanon
open import Fresh

PathDistinct-αc : ∀{t : Tm}{n : V}{ρ : Renaming} →
                  varsub (fvs t) (domr ρ) ≡ tt →
                  Ubounded (ranr ρ) n → 
                  PathDistinct (ranr ρ) (αc n ρ t) 
PathDistinct-αc {var x} {n} {ρ} sb bd = var (varmem-rename{x}{ρ} (&&-elim1 sb))
PathDistinct-αc {t1 · t2} {n} {ρ} sb bd rewrite varsub-++ {fvs t1} {fvs t2} {domr ρ} =
 app
   (PathDistinct-αc {t1} {ff :: n} {ρ} (&&-elim1 sb) (Ubounded-::{ranr ρ}{n}{ff} bd))
   (PathDistinct-αc {t2} {tt :: n} {ρ} (&&-elim2 sb) (Ubounded-::{ranr ρ}{n}{tt} bd))
PathDistinct-αc {ƛ x t} {n} {ρ} sb bd =
 lam (bounded-not-varmem {n} {ranr ρ} bd)
   (PathDistinct-αc {t} {ff :: n} {(x , n) :: ρ}
     (varsub-remove {fvs t} {domr ρ} {x} sb)
     ((Vargt-::2{n}{ff}) ,
       (Ubounded-::{ranr ρ}{n}{ff} bd)))

Lbounded-αc : ∀{t : Tm}{n m : V}{ρ : Renaming} →
              Varle n m → 
              Wlbounded (bvs (αc m ρ t)) n
Lbounded-αc {var x} {n}{m} {ρ} le = triv
Lbounded-αc {t1 · t2} {n}{m} {ρ} le =
  all-pred-append3{l1 = bvs (αc (ff :: m) ρ t1)}
    (Lbounded-αc {t1} {n} {ff :: m} {ρ} (Varle-::{n}{m}{ff} le)) 
    (Lbounded-αc {t2} {n} {tt :: m} {ρ} (Varle-::{n}{m}{tt} le))
Lbounded-αc {ƛ x t} {n}{m} {ρ} le = le , Lbounded-αc {t} {n} {ff :: m} {(x , m) :: ρ} (Varle-::{n}{m}{ff} le)

varunique-αc : ∀{t : Tm}{n : V}{ρ : Renaming} →
               varunique (bvs (αc n ρ t)) ≡ tt 
varunique-αc {var x} {n} {ρ} = refl
varunique-αc {t1 · t2} {n} {ρ} =
  varapart-++-varunique {bvs (αc (ff :: n) ρ t1)} {bvs (αc (tt :: n) ρ t2)}
    (disjoint-Pred {V} {Varle (ff :: n)} {Varle (tt :: n)} {_≃_}
      {bvs (αc (ff :: n) ρ t1)} {bvs (αc (tt :: n) ρ t2)}
        (Lbounded-αc {t1} {ff :: n} {ff :: n} {ρ} Suffix-refl)
        (Lbounded-αc {t2} {tt :: n} {tt :: n} {ρ} Suffix-refl)
        (λ{a} u v → Suffix-different {𝔹} {n} {a} {tt} {ff} (λ()) v u)
        Varle-cong)
    (varunique-αc{t1}{ff :: n}{ρ})
    (varunique-αc{t2}{tt :: n}{ρ})

varunique-αc {ƛ x t} {n} {ρ} =
 let l = bvs (αc (ff :: n) ((x , n) :: ρ) t) in
 let q = varmem n l in
  &&-intro {~ q}
   (~-≡-ff {q} (member-out-Pred {V} {Varle (ff :: n)} {_≃_} {n} {l} h
                 (Lbounded-αc{t}{ff :: n}{ff :: n}{(x , n) :: ρ} Suffix-refl)
                 Varle-cong))
   (varunique-αc{t}{ff :: n}{((x , n) :: ρ)})

 where h : Varle (ff :: n) n → ⊥
       h (y , eq) with cong length eq 
       h (y , eq) | u rewrite length-++ y (ff :: n) = +≢ (length n) (length y) h'
        where h' : length n ≡ length n + suc (length y)
              h' rewrite +suc (length n) (length y) | +suc (length y) (length n) | +comm (length n) (length y) = sym u

AllDistinct-αc : ∀{t : Tm}{n : V}{ρ : Renaming} →
                 varsub (fvs t) (domr ρ) ≡ tt →
                 Ubounded (ranr ρ) n → 
                 AllDistinct (ranr ρ) (αc n ρ t) 
AllDistinct-αc{t}{n}{ρ} sb ub = (varunique-αc{t}{n}{ρ}) , (PathDistinct-αc{t}{n}{ρ} sb ub)

PathDistinct-Apart' : ∀{t : Tm}{vs vs' : 𝕃 V} →
                PathDistinct vs' t →
                varsub vs vs' ≡ tt → 
                varapart vs (bvs t) ≡ tt
PathDistinct-Apart' {var x} {vs} {vs'} pd sb = varapart-[]{vs}
PathDistinct-Apart' {t1 · t2} {vs} {vs'} (app pd1 pd2) sb = varapart-++i {vs} {bvs t1} {bvs t2}
                                            (PathDistinct-Apart'{t1}{vs}{vs'} pd1 sb) 
                                            (PathDistinct-Apart'{t2}{vs}{vs'} pd2 sb) 
PathDistinct-Apart' {ƛ x t} {vs} {vs'} (lam u pd) sb = 
 varapart-++i {vs} {[ x ]} {bvs t}
   (varapart-sym {[ x ]} {vs} h )
   (PathDistinct-Apart' {t} {vs} {x :: vs'} pd (varsub-++2{[ x ]}{vs}{vs'} sb))
 where h : varapart [ x ] vs ≡ tt
       h rewrite varmem-varsub-ff{x}{vs}{vs'} sb (~-≡-tt {varmem x vs'} (~-≡-ff u)) = refl

PathDistinct-fvs : ∀{t : Tm}{vs : 𝕃 V} → 
                   PathDistinct vs t →
                   varsub (fvs t) vs ≡ tt 
PathDistinct-fvs {var x} {vs} (var u) rewrite u = refl
PathDistinct-fvs {t1 · t2} {vs} (app pd1 pd2) =
 varsub-++il {fvs t1} {fvs t2} {vs}
  (PathDistinct-fvs{t1}{vs} pd1)
  (PathDistinct-fvs{t2}{vs} pd2)
PathDistinct-fvs {ƛ x t} {vs} (lam _ pd) = varsub-remove1 {fvs t} {vs} {x} (PathDistinct-fvs{t}{x :: vs} pd)

fvs-αc : ∀{t : Tm}{n : V}{ρ : Renaming} →
         varsub (fvs t) (domr ρ) ≡ tt → 
         varsub (fvs (αc n ρ t)) (ranr ρ) ≡ tt
fvs-αc {var x}{n} {ρ} sb rewrite varmem-rename{x}{ρ} (&&-elim1 sb) = refl
fvs-αc {t1 · t2}{n} {ρ} sb rewrite varsub-++{fvs t1}{fvs t2}{domr ρ} =
 varsub-++il {fvs (αc (ff :: n) ρ t1)} {fvs (αc (tt :: n) ρ t2)} {ranr ρ}
    (fvs-αc{t1}{ff :: n}{ρ} (&&-elim1 sb)) (fvs-αc{t2}{tt :: n}{ρ} (&&-elim2 sb))
fvs-αc {ƛ x t}{n} {ρ} sb =
 varsub-remove1 {fvs (αc (ff :: n) ((x , n) :: ρ) t)} {ranr ρ} {n}
  (fvs-αc {t}{ff :: n} {(x , n) :: ρ} (varsub-remove {fvs t} {domr ρ} {x} sb))
