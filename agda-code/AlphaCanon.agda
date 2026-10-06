{-# OPTIONS --allow-unsolved-metas #-}
open import lib hiding (_>>=_ ; return ; _∘_)
open import relations
open import functions
open import diamond
open import VarInterface

module AlphaCanon where

open import Tm 
open import Renaming
open import Subst
open import Substitution hiding (_∘_)
open import Monad
open import AlphaM

αc : Tm → Renaming → Tm
αc (var x) ρ = var (rename ρ x)
αc (t1 · t2) ρ = αc t1 ρ · αc t2 ρ
αc (ƛ x t) ρ =
  let n = fresh (ranr ρ) in
    ƛ n (αc t ((x , n) :: ρ))

αcanon : Tm → Tm
αcanon t = αc t (diagonal (fvs t))

αa : Tm → αM Tm
αa (var x) = do
 v ← renamev x
 return (var v)
αa (t1 · t2) = do
 r1 ← αa t1
 r2 ← αa t2
 return (r1 · r2)
αa (ƛ x t) =
 withFresh x
   (λ n →
     do
      r ← αa t
      return (ƛ n r))

αaa : Tm → Renaming → 𝕃 V → Tm × 𝕃 V
αaa t ρ vs = runαm (αa t) ρ vs

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
allDistinct vs t = varunique (bvs t) && pathDistinct vs t 

αc-pathDistinct : ∀{t : Tm}{ρ : Renaming} →
             varsub (fvs t) (domr ρ) ≡ tt → 
             pathDistinct (ranr ρ) (αc t ρ) ≡ tt
αc-pathDistinct {var x}{ρ} sb = varmem-rename{x}{ρ} (&&-elim1 sb)
αc-pathDistinct {t1 · t2}{ρ} sb rewrite varsub-++{fvs t1}{fvs t2}{domr ρ} | αc-pathDistinct{t1}{ρ} (&&-elim1 sb) 
                               | αc-pathDistinct{t2}{ρ} (&&-elim2 sb) = refl
αc-pathDistinct {ƛ x t}{ρ} sb =
  &&-intro {~ varmem (fresh (ranr ρ)) (ranr ρ)} (~-≡-ff (fresh-distinct{ranr ρ})) 
   (αc-pathDistinct {t} {(x , fresh (ranr ρ)) :: ρ} (varsub-remove {fvs t} {domr ρ} {x} sb))

αa-allDistinct-Pre : Pre
αa-allDistinct-Pre ρ vs = varsub (ranr ρ) vs ≡ tt

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
    (&&-elim1 (&&-elim2{varunique (bvs t1 ++ bvs t2)} ad))

allDistinct-app2 : ∀{t1 t2 : Tm}{vs : 𝕃 V} →
                  allDistinct vs (t1 · t2) ≡ tt → 
                  allDistinct vs t2 ≡ tt
allDistinct-app2{t1}{t2}{vs} ad =
  &&-intro {varunique (bvs t2)}
    (varunique-++2 {bvs t1} {bvs t2} (&&-elim1{varunique (bvs t1 ++ bvs t2)} ad))
    (&&-elim2 (&&-elim2{varunique (bvs t1 ++ bvs t2)} ad))

allDistinct-lam : ∀{x : V}{t : Tm}{vs : 𝕃 V} →
                   allDistinct vs (ƛ x t) ≡ tt →
                  ~ varmem x vs ≡ tt ∧ allDistinct (x :: vs) t ≡ tt
allDistinct-lam{x}{t}{vs} ad with &&-elim{varunique (bvs (ƛ x t))} ad 
allDistinct-lam{x}{t}{vs} ad | p1 , p2 =
 (&&-elim1 p2) , (&&-intro {varunique (bvs t)} (&&-elim2 p1) (&&-elim2 p2))

all-to-path : ∀{t : Tm}{vs : 𝕃 V} →
              allDistinct vs t ≡ tt →
              pathDistinct vs t ≡ tt
all-to-path ad = &&-elim2 ad

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

Subst-var-graft1 : ∀{s1 s2 t1 t2 : Tm}{x y z : V}{vs : 𝕃 V} →
                   x ≃ z ≡ ff →
                   y ≃ z ≡ ff →
                   varmem x (bvs s2) ≡ ff →
                   varmem y (bvs s2) ≡ ff →                    
                   varsub (fvs s1) vs ≡ tt → 
                   pathDistinct vs s2 ≡ tt → 
                   Subst (var x) y s1 t1 →
                   Subst (var x) y s2 t2 →
                   Subst (var x) y (graft1 s1 z s2) (graft1 t1 z t2)
Subst-var-graft1 {s1} {var y} {t1} {var x} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 var-found rewrite ne3 | ne2 = var-found
Subst-var-graft1 {s1} {var w} {t1} {var w} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (var-not x₁) with keep (w ≃ z)
Subst-var-graft1 {s1} {var w} {t1} {var w} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (var-not x₁) | tt , eq rewrite eq = sb1
Subst-var-graft1 {s1} {var w} {t1} {var w} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (var-not x₁) | ff , eq rewrite eq =
 var-not x₁
Subst-var-graft1 {s1} {sa · sb} {t1} {ta · tb} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (app sb2 sb3)
  rewrite varmem-++ y (bvs sa) (bvs sb) | varmem-++ x (bvs sa) (bvs sb) =
  app (Subst-var-graft1 {s1} {sa} {t1} {ta} {x} {y} {z} {vs}
        ne2 ne3 (fst (||-≡-ff{varmem x (bvs sa)} nx)) (fst (||-≡-ff{varmem y (bvs sa)} ny)) fv
        (&&-elim1 pd) sb1 sb2)
      (Subst-var-graft1 {s1} {sb} {t1} {tb} {x} {y} {z} {vs}
        ne2 ne3 (snd (||-≡-ff{varmem x (bvs sa)} nx)) (snd (||-≡-ff{varmem y (bvs sa)} ny)) fv
        (&&-elim2 pd) sb1 sb3) 
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w t2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-go x₁ x₂ sb2)
  with ∈ƛ{y}{w}{s2} x₁
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w t2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-go x₁ x₂ sb2) | i1 , i2
 with keep (z ≃ w) 
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w t2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1
 (lam-go x₁ x₂ sb2) | i1 , i2 | tt , eq rewrite eq | graft-[] {s2} | graft-[] {t2} =
  lam-go x₁ x₂ sb2
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w t2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1
 (lam-go x₁ x₂ sb2) | i1 , i2 | ff , eq rewrite eq =
 lam-go h x₂
  (Subst-var-graft1 {s1} {s2} {t1} {t2} {x} {y} {z} {w :: vs}
    ne2 ne3 (snd (||-≡-ff{x ≃ w} nx)) (snd (||-≡-ff{y ≃ w} ny))
    (varsub-++2 {[ w ]} {fvs s1} {vs} fv)
    (&&-elim2 pd) sb1 sb2)
 where h : y ∈ ƛ w (graft ((z , s1) :: []) s2) ≡ tt
       h rewrite varmem-remove3{y}{w}{fvs (graft1 s1 z s2)} i1 (graft-∈ {y} {z} {s1} {s2} ne3 i2) = refl
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
 with keep (y ∈ s1) | keep (z ≃ w) 
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | tt , nn | tt , zw rewrite zw | graft-[] {s2} = lam-stop x₁
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | tt , nn | ff , zw rewrite zw with keep (z ∈ s2)
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | tt , nn | ff , zw | tt , z2 with ∈ƛff{y}{w}{s2} x₁ 
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | tt , nn | ff , zw | tt , z2 | inj₁ i rewrite ≃-≡{y} i | varmem-varsub{w}{fvs s1}{vs} nn fv with pd
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | tt , nn | ff , zw | tt , z2 | inj₁ i | ()
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | tt , nn | ff , zw | tt , z2 | inj₂ (i1 , i2) =
  lam-go h' h
    (Subst-var-graft1 {s1} {s2} {t1} {s2} {x} {y} {z} {w :: vs}
       ne2 ne3 (snd (||-≡-ff{x ≃ w} nx)) (snd (||-≡-ff{y ≃ w} ny))
       (varsub-++2 {[ w ]} {fvs s1} {vs} fv) (&&-elim2 pd)
       sb1 (Subst-refl {var x} {s2} {y} i2))
  where h : w ∈ var x ≡ ff
        h rewrite ~≃-sym{x} (fst (||-≡-ff{x ≃ w} nx)) = refl
        h' : y ∈ ƛ w (graft ((z , s1) :: []) s2) ≡ tt
        h' rewrite varmem-remove-neq{y}{w}{fvs (graft1 s1 z s2)} i1 =
          fvs-∈-graft {s1} {s2} {y} {z} nn z2 (snd (||-≡-ff{y ≃ w} ny))
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | tt , nn | ff , zw | ff , z2 with varmem-remove-neq{y}{w}{fvs s2} (fst (||-≡-ff{y ≃ w} ny))
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | tt , nn | ff , zw | ff , z2 | rm
  rewrite rm
        | graft-~∈{z}{s1}{s2} z2
        | graft-~∈{z}{t1}{s2} z2 = Subst-refl {var x} {ƛ w s2} {y} h
  where h : varmem y (varrem w (fvs s2)) ≡ ff
        h rewrite rm = x₁
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | ff , nn | tt , zw rewrite zw | graft-[] {s2} = lam-stop x₁
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | ff , nn | ff , zw with Subst-not-found{var x}{s1}{t1}{y} sb1 nn
Subst-var-graft1 {s1} {ƛ w s2} {t1} {ƛ w s2} {x} {y} {z} {vs} ne2 ne3 nx ny fv pd sb1 (lam-stop x₁)
  | ff , nn | ff , zw | refl rewrite zw | varmem-remove-neq{y}{w}{fvs s2} (fst (||-≡-ff{y ≃ w} ny))
             = lam-stop h
  where h' : varmem y (varrem z (fvs s2) ++ fvs s1) ≡ ff
        h' rewrite varmem-++ y (varrem z (fvs s2)) (fvs s1) | nn | varmem-remove-neq{y}{z}{fvs s2} ne3 | x₁ = refl
        h : y ∈ ƛ w (graft ((z , s1) :: []) s2) ≡ ff
        h rewrite varmem-remove-neq{y}{w}{fvs (graft1 s1 z s2)} (fst (||-≡-ff{y ≃ w} ny)) =
          varmem-varsub-ff {y} {fvs (graft1 s1 z s2)}
           {varrem z (fvs s2) ++ fvs s1} (fvs-graft{z}{s2}{s1}) h'

{-
pathDistinct-Subst-var : ∀{x y : V}{vs : 𝕃 V}{r s : Tm} →
                         y ∈ r ≡ ff → 
                         pathDistinct (y :: vs) s ≡ tt →
                         Subst (var y) x r s →
                         pathDistinct (x :: vs) r ≡ tt 
pathDistinct-Subst-var {x} {y} {vs} {var x} {var y} _ _ var-found rewrite ≃-refl{x} = refl
pathDistinct-Subst-var {x} {y} {vs} {var z} {var z} ni pd (var-not ne)
 rewrite ~≃-sym{x} ne | ||-ff (y ≃ z) with ||-elim{z ≃ y} pd
pathDistinct-Subst-var {x} {y} {vs} {var z} {var z} ni pd (var-not ne) | inj₁ i rewrite ≃-≡{z} i | ≃-refl{y} with ni
pathDistinct-Subst-var {x} {y} {vs} {var z} {var z} ni pd (var-not ne) | inj₁ i | ()
pathDistinct-Subst-var {x} {y} {vs} {var z} {var z} ni pd (var-not ne) | inj₂ i = i
pathDistinct-Subst-var {x} {y} {vs} {r1 · r2} {s1 · s2} ni pd (app sb1 sb2) rewrite varmem-++ y (fvs r1) (fvs r2)
 rewrite pathDistinct-Subst-var{x}{y}{vs}{r1}{s1} (fst (||-≡-ff{y ∈ r1} ni)) (&&-elim1 pd) sb1 =
 pathDistinct-Subst-var {x} {y} {vs} {r2} {s2}
  (snd (||-≡-ff{y ∈ r1} ni)) (&&-elim2 pd) sb2
pathDistinct-Subst-var {x} {y} {vs} {ƛ z r} {ƛ z s} ni pd (lam-go x₁ x₂ sb) =
  {!!} -- x can't be z because x ∈ ƛ z r
pathDistinct-Subst-var {x} {y} {vs} {ƛ z r} {ƛ z r} yni pd (lam-stop xni) with ∈ƛff{x}{z}{r} xni
pathDistinct-Subst-var {x} {y} {vs} {ƛ z r} {ƛ z r} yni pd (lam-stop xni) | inj₁ i rewrite ≃-≡{x} i = {!!}
pathDistinct-Subst-var {x} {y} {vs} {ƛ z r} {ƛ z r} yni pd (lam-stop xni) | inj₂ i = {!!}
-}

pathDistinct-fvs : ∀{t : Tm}{vs : 𝕃 V} → 
                   pathDistinct vs t ≡ tt →
                   varsub (fvs t) vs ≡ tt 
pathDistinct-fvs {var x} {vs} pd rewrite pd = refl
pathDistinct-fvs {t1 · t2} {vs} pd =
 varsub-++il {fvs t1} {fvs t2} {vs}
  (pathDistinct-fvs{t1}{vs} (&&-elim1 pd))
  (pathDistinct-fvs{t2}{vs} (&&-elim2 pd))
pathDistinct-fvs {ƛ x t} {vs} pd = varsub-remove1 {fvs t} {vs} {x} (pathDistinct-fvs{t}{x :: vs} (&&-elim2 pd))


αP : Tm → Set
αP t = (ρ : Renaming)(vs : 𝕃 V) →
        varsub (fvs t) (domr ρ) ≡ tt →
        varsub (ranr ρ) vs ≡ tt →

           Σ (Tm × 𝕃 ℕ) (λ r → 
           Σ (𝕃 V) (λ i →
           let t' = fst r in
           let vs' = snd r in
            r ≡ runαm{Tm} (αa t) ρ vs ∧ 
            vs' ≡ vs ++ i ∧
            varsub (fvs t') (ranr ρ) ≡ tt ∧
            varapart vs i ≡ tt ∧
            varsub (bvs t') i ≡ tt ∧ 
            varunique (bvs t') ≡ tt ))

αa-thm : ∀{t : Tm} → αP t
αa-thm {var x} ρ vs sub1 sub2 =
  (var (rename ρ x) , vs) , [] , refl , sym (++[] vs) , &&-intro (varmem-rename{x}{ρ} (&&-elim1 sub1)) refl  , (varapart-[]{vs}) , (refl , refl)
αa-thm {t1 · t2} ρ vs sub1 sub2 with αa-thm {t1} ρ vs {!!} {!!} 
αa-thm {t1 · t2} ρ vs sub1 sub2 | r1 , i , req , ieq , sub' , ap , bsub , buni with αa-thm {t2} ρ (snd r1) {!!} {!!} 
αa-thm {t1 · t2} ρ vs sub1 sub2 | r1 , i , req , ieq , sub' , ap , bsub , buni | r2 , i2 , req2 , ieq2 , sub2' , ap2 , bsub2 , buni2
 rewrite sym req | sym req2 =
 (fst r1 · fst r2 , snd r2 ), i ++ i2 , refl , h1 , {!!} , {!!} , {!!} , varapart-++-varunique{bvs (fst r1)} {!!}
 where h1 : snd r2 ≡ vs ++ i ++ i2
       h1 rewrite ieq2 | ieq = ++-assoc vs i i2
αa-thm {ƛ x t} ρ vs sub1 sub2 = {!!}