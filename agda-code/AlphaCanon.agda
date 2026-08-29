open import lib hiding (_>>=_ ; return ; _∘_)
open import relations
open import diamond
open import VarInterface

module AlphaCanon where

open import Tm 
open import Renaming
open import Subst

αc : Tm → Renaming → Tm
αc (var x) ρ = var (rename ρ x)
αc (t1 · t2) ρ = αc t1 ρ · αc t2 ρ
αc (ƛ x t) ρ =
  let n = fresh (ranr ρ) in
    ƛ n (αc t ((x , n) :: ρ))

αcanon : Tm → Tm
αcanon t = αc t (diagonal (fvs t))

{- pathDistinct vs t

   This means that the variables in vs are not bound in t
   and hereditarily for subterms of t where we add the bound
   variables above those subterms, to vs.

   So if x is bound somewhere in t, then it cannot be bound again
   below that point.

   This explains the name: the bound variables along each path into
   the term are distinct (and different from the variables in vs)
-}
pathDistinct : 𝕃 V → Tm → 𝔹
pathDistinct vs (var x) = varmem x vs
pathDistinct vs (t1 · t2) = pathDistinct vs t1 && pathDistinct vs t2
pathDistinct vs (ƛ x t) = ~ varmem x vs && pathDistinct (x :: vs) t

{- all bound variables are distinct from each other and all the
   free variables.

   The implementation collects the list of all bound variables
   by binding occurrence, and then insists that there are no duplicates.
   So the same variable cannot be bound twice.
-}
allDistinct : 𝕃 V → Tm → 𝔹
allDistinct vs t =
 let bs = bvs t in
  varunique bs && varapart bs vs && varsub (fvs t) vs

αc-pathDistinct : ∀{t : Tm}{ρ : Renaming} →
             varsub (fvs t) (domr ρ) ≡ tt → 
             pathDistinct (ranr ρ) (αc t ρ) ≡ tt
αc-pathDistinct {var x}{ρ} sb = varmem-rename{x}{ρ} (&&-elim1 sb)
αc-pathDistinct {t1 · t2}{ρ} sb rewrite varsub-++{fvs t1}{fvs t2}{domr ρ} | αc-pathDistinct{t1}{ρ} (&&-elim1 sb) 
                               | αc-pathDistinct{t2}{ρ} (&&-elim2 sb) = refl
αc-pathDistinct {ƛ x t}{ρ} sb =
  &&-intro {~ varmem (fresh (ranr ρ)) (ranr ρ)} (~-≡-ff (fresh-distinct{ranr ρ})) 
   (αc-pathDistinct {t} {(x , fresh (ranr ρ)) :: ρ} (varsub-remove {fvs t} {domr ρ} {x} sb))

pathDistinct-Apart' : ∀{t : Tm}{vs vs' : 𝕃 V} →
                pathDistinct vs' t ≡ tt →
                varsub vs vs' ≡ tt → 
                varapart vs (bvs t) ≡ tt
pathDistinct-Apart' {var x} {vs} {vs'} ok sb = varapart-[]{vs}
pathDistinct-Apart' {t1 · t2} {vs} {vs'} ok sb = varapart-++i {vs} {bvs t1} {bvs t2}
                                            (pathDistinct-Apart'{t1}{vs}{vs'} (&&-elim1 ok) sb) 
                                            (pathDistinct-Apart'{t2}{vs}{vs'} (&&-elim2 ok) sb) 
pathDistinct-Apart' {ƛ x t} {vs} {vs'} ok sb = 
 varapart-++i {vs} {[ x ]} {bvs t}
   (varapart-sym {[ x ]} {vs} h )
   (pathDistinct-Apart' {t} {vs} {x :: vs'} (&&-elim2 ok) (varsub-++2{[ x ]}{vs}{vs'} sb))
 where h : varapart [ x ] vs ≡ tt
       h rewrite varmem-varsub-ff{x}{vs}{vs'} sb (~-≡-tt {varmem x vs'} (&&-elim1 ok)) = refl

fvs-αc : ∀{t : Tm}{ρ : Renaming} →
         varsub (fvs t) (domr ρ) ≡ tt → 
         varsub (fvs (αc t ρ)) (ranr ρ) ≡ tt
fvs-αc {var x} {ρ} sb rewrite varmem-rename{x}{ρ} (&&-elim1 sb) = refl
fvs-αc {t1 · t2} {ρ} sb rewrite varsub-++{fvs t1}{fvs t2}{domr ρ} =
 varsub-++il {fvs (αc t1 ρ)} {fvs (αc t2 ρ)} {ranr ρ}
    (fvs-αc{t1}{ρ} (&&-elim1 sb)) (fvs-αc{t2}{ρ} (&&-elim2 sb))
fvs-αc {ƛ x t} {ρ} sb = varsub-remove1 {fvs (αc t ((x , fresh (ranr ρ)) :: ρ))} {ranr ρ}
                         {fresh (ranr ρ)} (fvs-αc {t} {(x , fresh (ranr ρ)) :: ρ} (varsub-remove {fvs t} {domr ρ} {x} sb))

allDistinct-app1 : ∀{t1 t2 : Tm}{vs : 𝕃 V} →
                  allDistinct vs (t1 · t2) ≡ tt → 
                  allDistinct vs t1 ≡ tt
allDistinct-app1{t1}{t2}{vs} ad =
  &&-intro {varunique (bvs t1)}
    (varunique-++1 {bvs t1} {bvs t2} (&&-elim1{varunique (bvs t1 ++ bvs t2)} ad))
    (&&-intro {varapart (bvs t1) vs}
       (fst (varapart-++2{bvs t1}{bvs t2}{vs} (&&-elim1 (&&-elim2{varunique (bvs (t1 · t2))} ad)) ))
       (varsub-++1l {fvs t1} {fvs t2} {vs} (&&-elim2 (&&-elim2{varunique (bvs (t1 · t2))} ad))))

allDistinct-app2 : ∀{t1 t2 : Tm}{vs : 𝕃 V} →
                  allDistinct vs (t1 · t2) ≡ tt → 
                  allDistinct vs t2 ≡ tt
allDistinct-app2{t1}{t2}{vs} ad =
  &&-intro {varunique (bvs t2)}
    (varunique-++2 {bvs t1} {bvs t2} (&&-elim1{varunique (bvs t1 ++ bvs t2)} ad))
    (&&-intro {varapart (bvs t2) vs}
      (snd (varapart-++2{bvs t1}{bvs t2}{vs} (&&-elim1 (&&-elim2{varunique (bvs (t1 · t2))} ad)) ))
      (varsub-++2l {fvs t1} {fvs t2} {vs} (&&-elim2 (&&-elim2{varunique (bvs (t1 · t2))} ad))))

allDistinct-lam : ∀{x : V}{t : Tm}{vs : 𝕃 V} →
                   allDistinct vs (ƛ x t) ≡ tt →
                  ~ varmem x vs ≡ tt ∧ allDistinct (x :: vs) t ≡ tt
allDistinct-lam{x}{t}{vs} ad with &&-elim{varunique (bvs (ƛ x t))} ad 
allDistinct-lam{x}{t}{vs} ad | p1 , p2 with &&-elim{varapart (bvs (ƛ x t)) vs} p2 
allDistinct-lam{x}{t}{vs} ad | p1 , p2 | p2a , p2b =
  &&-elim1 p2a ,
  &&-intro (&&-elim2{~ varmem x (bvs t)} p1) 
   (&&-intro {varapart (bvs t) (x :: vs)} (varapart-sym {x :: vs} {bvs t} 
     (&&-intro {~ varmem x (bvs t)} (&&-elim1 p1) (varapart-sym {bvs t} {vs} (&&-elim2 p2a))))
     (varsub-remove{fvs t}{vs}{x} p2b)) 

all-to-path : ∀{t : Tm}{vs : 𝕃 V} →
              allDistinct vs t ≡ tt →
              pathDistinct vs t ≡ tt
all-to-path {var x} {vs} ad =
 &&-elim1{varmem x vs} (&&-elim2 {varunique []} (&&-elim2 {varapart [] vs}{varsub [ x ] vs} ad))
all-to-path {t1 · t2} {vs} ad =
  &&-intro {pathDistinct vs t1}
    (all-to-path{t1}{vs} (allDistinct-app1{t1}{t2}{vs} ad))
    (all-to-path{t2}{vs} (allDistinct-app2{t1}{t2}{vs} ad))
all-to-path {ƛ x t} {vs} ad with allDistinct-lam{x}{t}{vs} ad
all-to-path {ƛ x t} {vs} ad | p1 , p2 rewrite p1 | all-to-path{t}{x :: vs} p2 = refl

pathDistinct-collapse : ∀{x y : V}{vs1 vs2 vs3 : 𝕃 V}{t : Tm} →
                        pathDistinct (vs1 ++ y :: vs2 ++ x :: vs3) t ≡ tt → 
                        x ≃ y ≡ tt → 
                        pathDistinct (vs1 ++ y :: vs2 ++ vs3) t ≡ tt
pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {var z} di eq
  rewrite varmem-++ z vs1 (y :: vs2 ++ vs3) | varmem-++ z vs2 vs3
        | varmem-++ z vs1 (y :: vs2 ++ x :: vs3) | varmem-++ z vs2 (x :: vs3) with keep (z ≃ y)
pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {var z} di eq | tt , eq' rewrite eq' = ||-tt (varmem z vs1)
pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {var z} di eq | ff , eq' rewrite eq' | ≃-≡{x} eq | eq' = di
pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {t1 · t2} di eq
 rewrite pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {t1} (&&-elim1 di) eq =
 pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {t2} (&&-elim2 di) eq
pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {ƛ z t} di eq
 rewrite varmem-++ z vs1 (y :: vs2 ++ vs3) | varmem-++ z vs2 vs3
       | varmem-++ z vs1 (y :: vs2 ++ x :: vs3) | varmem-++ z vs2 (x :: vs3)
       | ~||&&{varmem z vs1}{z =ℕ y || list-member _=ℕ_ z vs2 || list-member _=ℕ_ z vs3}
       | ~||&&{z ≃ y}{list-member _=ℕ_ z vs2 || list-member _=ℕ_ z vs3}
       | ~||&&{list-member _=ℕ_ z vs2}{list-member _=ℕ_ z vs3} 
       | ~||&&{varmem z vs1}{z =ℕ y || list-member _=ℕ_ z vs2 || z ≃ x || list-member _=ℕ_ z vs3}
       | ~||&&{z ≃ y}{list-member _=ℕ_ z vs2 || z ≃ x || list-member _=ℕ_ z vs3}
       | ~||&&{list-member _=ℕ_ z vs2}{z ≃ x || list-member _=ℕ_ z vs3} 
       | ~||&&{z ≃ x}{list-member _=ℕ_ z vs3}
  with z ≃ x | ~ varmem z vs1 | ~ z ≃ y | ~ varmem z vs2 | ~ varmem z vs3
pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {ƛ z t} di eq | tt | p1 | p2 | p3 | p4 with &&-elim1{p1 && p2 && p3 && ff} di 
pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {ƛ z t} di eq | tt | p1 | p2 | p3 | p4 | p5 rewrite &&-ff p3 | &&-ff p2 | &&-ff p1 with p5
pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {ƛ z t} di eq | tt | p1 | p2 | p3 | p4 | p5 | ()
pathDistinct-collapse {x} {y} {vs1} {vs2} {vs3} {ƛ z t} di eq | ff | p1 | p2 | p3 | p4 =
  &&-intro {p1 && p2 && p3 && p4} (&&-elim1 di) (pathDistinct-collapse{x}{y}{z :: vs1}{vs2}{vs3}{t} (&&-elim2 di) eq)


pathDistinct-not-bound : ∀{x : V}{vs1 vs2 : 𝕃 V}{t : Tm} →
                        varmem x (bvs t) ≡ ff →
                        pathDistinct (vs1 ++ vs2) t ≡ tt → 
                        pathDistinct (vs1 ++ x :: vs2) t ≡ tt
pathDistinct-not-bound {x} {vs1} {vs2} {var z} _ u rewrite varmem-++ z vs1 (x :: vs2) | varmem-++ z vs1 vs2 with z ≃ x
pathDistinct-not-bound {x} {vs1} {vs2} {var z} _ u | tt rewrite ||-tt (varmem z vs1) = refl
pathDistinct-not-bound {x} {vs1} {vs2} {var z} _ u | ff = u
pathDistinct-not-bound {x} {vs1} {vs2} {t1 · t2} n u rewrite varmem-++ x (bvs t1) (bvs t2) =
  let p = ||-ff-elim{varmem x (bvs t1)} n in
   &&-intro {pathDistinct (vs1 ++ x :: vs2) t1} 
    (pathDistinct-not-bound {x} {vs1} {vs2} {t1}
     (fst p)
     (&&-elim1 u))
    (pathDistinct-not-bound {x} {vs1} {vs2} {t2}
     (snd p)
     (&&-elim2 u))
pathDistinct-not-bound {x} {vs1} {vs2} {ƛ y t} n u rewrite varmem-++ x [ y ] (bvs t) | ||-ff (x ≃ y) | varmem-++ y vs1 (x :: vs2)
 | varmem-++ y [ x ] vs2 with ||-ff-elim{x ≃ y} n 
pathDistinct-not-bound {x} {vs1} {vs2} {ƛ y t} n u | p rewrite ~≃-sym{x} (fst p) | varmem-++ y vs1 vs2 =
  &&-intro {~ (varmem y vs1 || varmem y vs2)}
    (&&-elim1 u)
    (pathDistinct-not-bound {x} {y :: vs1} {vs2}{t} (snd p) (&&-elim2 u))

pathDistinct-not-free : ∀{x : V}{vs1 vs2 : 𝕃 V}{t : Tm} →
                        pathDistinct (vs1 ++ x :: vs2) t ≡ tt → 
                        varmem x (fvs t) ≡ ff →
                        pathDistinct (vs1 ++ vs2) t ≡ tt
pathDistinct-not-free {x} {vs1} {vs2} {var z} di m rewrite varmem-++ z vs1 (x :: vs2) | ||-ff (x ≃ z) | ~≃-sym{x} m | varmem-++ z vs1 vs2 = di
pathDistinct-not-free {x} {vs1} {vs2} {t1 · t2} di m rewrite varmem-++ x (fvs t1) (fvs t2) with ||-ff-elim{varmem x (fvs t1)} m 
pathDistinct-not-free {x} {vs1} {vs2} {t1 · t2} di m | m1 , m2 = 
  &&-intro{pathDistinct (vs1 ++ vs2) t1}
    (pathDistinct-not-free {x} {vs1} {vs2} {t1} (&&-elim1 di) m1)
    (pathDistinct-not-free {x} {vs1} {vs2} {t2} (&&-elim2 di) m2)
pathDistinct-not-free {x} {vs1} {vs2} {ƛ y t} di m rewrite  varmem-++ y vs1 (x :: vs2) with ||-ff-elim{varmem y vs1} (~-≡-tt (&&-elim1 di)) 
pathDistinct-not-free {x} {vs1} {vs2} {ƛ y t} di m | da , db rewrite varmem-++ y vs1 vs2 | da | snd (||-ff-elim{y ≃ x} db)
  =
  pathDistinct-not-free{x}{y :: vs1}{vs2}{t} (&&-elim2 di) h
  where h : varmem x (fvs t) ≡ ff
        h rewrite sym (varmem-remove-neq{x}{y}{fvs t} (~≃-sym{y} (fst (||-ff-elim db)))) = m

pathDistinct-Subst : ∀{t1 t2 t : Tm}{x : V}{vs1 vs2 : 𝕃 V} →
                     pathDistinct (vs1 ++ vs2) t1 ≡ tt →
                     pathDistinct (vs1 ++ x :: vs2) t2 ≡ tt →                      
                     varapart (bvs t1) (bvs t2) ≡ tt → 
                     Subst t1 x t2 t →
                     pathDistinct (vs1 ++ vs2) t ≡ tt
pathDistinct-Subst {t1} {var x} {t} {x} {vs1} {vs2} pd1 pd2 ap var-found = pd1
pathDistinct-Subst {t1} {var y} {t} {x} {vs1} {vs2} pd1 pd2 ap (var-not ne)
  rewrite varmem-++ y vs1 (x :: vs2) | varmem-++ y vs1 vs2 rewrite ~≃-sym{x} ne = pd2
pathDistinct-Subst {t1} {ta · tb} {ta' · tb'} {x} {vs1} {vs2} pd1 pd2 ap (app sb1 sb2)
  with varapart-++{bvs t1}{bvs ta}{bvs tb} ap
pathDistinct-Subst {t1} {ta · tb} {ta' · tb'} {x} {vs1} {vs2} pd1 pd2 ap (app sb1 sb2) | ap1 , ap2 
  rewrite pathDistinct-Subst{t1}{ta}{ta'}{x}{vs1} {vs2} pd1 (&&-elim1 pd2) ap1 sb1 =
  pathDistinct-Subst{t1}{tb}{tb'}{x}{vs1} {vs2} pd1 (&&-elim2 pd2) ap2 sb2

pathDistinct-Subst {t1} {ƛ y t2} {ƛ y t} {x} {vs1} {vs2} pd1 pd2 ap (lam-go xf nc sb) with ∈ƛ{x}{y}{t2} xf 
pathDistinct-Subst {t1} {ƛ y t2} {ƛ y t} {x} {vs1} {vs2} pd1 pd2 ap (lam-go xf nc sb) | p1 , p2
 rewrite varmem-++ y vs1 (x :: vs2) | ~≃-sym{x} p1 | varmem-++ y vs1 vs2 = 
 &&-intro {~ (varmem y vs1 || varmem y vs2)} 
   (&&-elim1 pd2)
   (pathDistinct-Subst {t1} {t2} {t} {x} {y :: vs1} {vs2}
     h (&&-elim2 pd2)
     (varapart-varsub {bvs t1} {bvs t1} {bvs t2} {y :: bvs t2} (varsub-refl{bvs t1}) (varsub-++2a{[ y ]}{bvs t2}) ap) sb)
 where h : pathDistinct (y :: vs1 ++ vs2) t1 ≡ tt
       h with varapart-sym{bvs t1}{y :: bvs t2} ap
       h | qq = pathDistinct-not-bound {y} {[]} {vs1 ++ vs2} {t1} (~-≡-tt (&&-elim1 qq)) pd1 
pathDistinct-Subst {t1} {ƛ y t2} {ƛ y t2} {x} {vs1} {vs2} pd1 pd2 ap (lam-stop nf) =
 &&-intro {~ varmem y (vs1 ++ vs2)}
   (~-≡-ff {varmem y (vs1 ++ vs2)}
     (varmem-varsub-ff {y} {vs1 ++ vs2} {vs1 ++ x :: vs2}
      (varsub-++-cong {vs1} {vs2} {x :: vs2} (varsub-++2a{[ x ]}{vs2}))
        (~-≡-tt{varmem y (vs1 ++ x :: vs2)} (&&-elim1 pd2)))) h

 where h : pathDistinct (y :: vs1 ++ vs2) t2 ≡ tt
       h with varmem-remove2{x}{y}{fvs t2} nf | &&-elim2{~ varmem y (vs1 ++ x :: vs2)} pd2
       h | inj₁ i | q = pathDistinct-collapse {x} {y} {[]} {vs1} {vs2} {t2} q i
       h | inj₂ i | q = pathDistinct-not-free{x}{y :: vs1}{vs2}{t2} (&&-elim2 pd2) i

