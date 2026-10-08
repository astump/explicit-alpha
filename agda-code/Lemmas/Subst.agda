open import lib
open import VarInterface

module Lemmas.Subst(vi : VI) where

open VI vi

open import Tm vi
open import Subst vi
open import Substitution vi
open import Apart vi
open import VarOps vi

open import Lemmas.VarOps vi
open import Lemmas.Tm vi
open import Lemmas.VarInterface vi
open import Lemmas.Apart vi
open import Lemmas.Substitution vi

substLem : ∀{t s : Tm}{x : V} →
           Apart t (bvs s) ≡ tt → 
           Subst t x s (graft1 t x s)
substLem {t} {var y}   {x} ap with keep (x ≃ y)
substLem {t} {var y}   {x} ap | tt , eq rewrite ≃-≡{x} eq | ≃-refl{y} = var-found
substLem {t} {var y}   {x} ap | ff , eq rewrite ~≃-sym{x} eq = var-not eq
substLem {t} {t1 · t2} {x} ap = app (substLem {t} {t1} {x} (Apart-++1{t}{bvs t1}{bvs t2} ap))
                                    (substLem {t} {t2} {x} (Apart-++2{t}{bvs t1}{bvs t2} ap))
substLem {t} {ƛ y t1}  {x} ap with keep (x ≃ y)
substLem {t} {ƛ y t1}  {x} ap | tt , eq rewrite eq | graft-[]{t1} = lam-stop h
 where h : x ∈ ƛ y t1 ≡ ff
       h rewrite ≃-≡{x} eq = varmem-remove-same{y}{fvs t1}
substLem {t} {ƛ y t1}  {x} ap | ff , eq rewrite eq with keep (x ∈ t1)
substLem {t} {ƛ y t1}  {x} ap | ff , eq | tt , eq' = lam-go h (~-≡-tt{varmem y (fvs t)} (&&-elim1 ap)) (substLem{t}{t1}{x} (&&-elim2 ap))
  where h : x ∈ ƛ y t1 ≡ tt
        h = varmem-remove3{x}{y}{fvs t1} eq eq'
--  lam-go (&&-intro{~ x ≃ y} (~-≡-ff eq) eq') (~-≡-tt (&&-elim1 ap)) (substLem{t}{t1}{x} (&&-elim2 ap))
substLem {t} {ƛ y t1}  {x} ap | ff , eq | ff , eq' rewrite graft-~∈{x}{t}{t1} eq' = lam-stop (varmem-remove4{x}{y}{fvs t1} eq eq')

subst-bvs : ∀{t1 t2 t : Tm}{x : V} →
            Subst t1 x t2 t →
            varsub (bvs t) (bvs t1 ++ bvs t2) ≡ tt
subst-bvs {t1} {var x} {t} {x} var-found rewrite ++[] (bvs t1) = varsub-refl {bvs t1}
subst-bvs {t1} {var y} {t} {x} (var-not x₂) = refl
subst-bvs {t1} {ta · tb} {ta' · tb'} {x} (app sb1 sb2) =
 varsub-++il {bvs ta'} {bvs tb'} {bvs t1 ++ bvs ta ++ bvs tb}
   h (varsub-trans {bvs tb'} {bvs t1 ++ bvs tb}
       {bvs t1 ++ bvs ta ++ bvs tb} (subst-bvs{t1}{tb}{tb'} sb2)
       (varsub-++-cong {bvs t1} {bvs tb} {bvs ta ++ bvs tb} (varsub-++2a{bvs ta}{bvs tb})))
 where h : varsub (bvs ta') (bvs t1 ++ bvs ta ++ bvs tb) ≡ tt
       h rewrite sym (++-assoc (bvs t1)(bvs ta)(bvs tb)) = varsub-++3 {bvs ta'} {bvs t1 ++ bvs ta} {bvs tb} (subst-bvs{t1}{ta}{ta'}{x} sb1)
subst-bvs {t1} {ƛ y t2} {ƛ y t} {x} (lam-go x₂ x₃ sb) =
  varsub-++il {[ y ]} {bvs t} {bvs t1 ++ y :: bvs t2}
    (varsub-++2 {bvs t1} {[ y ]} {y :: bvs t2} (varsub-++1{[ y ]}{bvs t2}))
      (varsub-trans {bvs t} {bvs t1 ++ bvs t2} {bvs t1 ++ y :: bvs t2} 
        (subst-bvs{t1}{t2}{t}{x} sb)
        (varsub-++-cong {bvs t1} {bvs t2} {y :: bvs t2} (varsub-++2a{[ y ]}{bvs t2})))
subst-bvs {t1} {ƛ y t2} {t} {x} (lam-stop x₂) = varsub-++2a{bvs t1}{y :: bvs t2}

Subst-det : ∀{t1 t2 ra rb : Tm}{y : V} →
            Subst t1 y t2 ra →
            Subst t1 y t2 rb →
            ra ≡ rb
Subst-det {t1} {var x} {ra} {rb} {y} var-found var-found = refl
Subst-det {t1} {var x} {ra} {rb} {y} var-found (var-not x₁) rewrite ≃-refl{x} with x₁ 
Subst-det {t1} {var x} {ra} {rb} {y} var-found (var-not x₁) | ()
Subst-det {t1} {var x} {ra} {rb} {y} (var-not x₁) var-found rewrite ≃-refl{x} with x₁ 
Subst-det {t1} {var x} {ra} {rb} {y} (var-not x₁) var-found | ()
Subst-det {t1} {var x} {ra} {rb} {y} (var-not x₁) (var-not x₂) = refl
Subst-det {t1} {ta · tb} {ta1 · tb1} {ta2 · tb2} {y} (app sba1 sba2) (app sbb1 sbb2)
 rewrite Subst-det{t1}{ta}{ta1}{ta2}{y} sba1 sbb1 | Subst-det{t1}{tb}{tb1}{tb2}{y} sba2 sbb2
 = refl
Subst-det {t1} {ƛ x t2} {ƛ x ra} {ƛ x rb} {y} (lam-go x₁ x₂ sb1) (lam-go x₃ x₄ sb2)
 rewrite Subst-det{t1}{t2}{ra}{rb}{y} sb1 sb2 = refl
Subst-det {t1} {ƛ x t2} {ƛ x ra} {rb} {y} (lam-go x₁ x₂ sb1) (lam-stop x₃) rewrite x₁ with x₃ 
Subst-det {t1} {ƛ x t2} {ƛ x ra} {rb} {y} (lam-go x₁ x₂ sb1) (lam-stop x₃) | ()
Subst-det {t1} {ƛ x t2} {ƛ x t2} {rb} {y} (lam-stop x₁) (lam-go x₂ x₃ sb2) rewrite x₁ with x₂ 
Subst-det {t1} {ƛ x t2} {ƛ x t2} {rb} {y} (lam-stop x₁) (lam-go x₂ x₃ sb2) | ()
Subst-det {t1} {ƛ x t2} {ƛ x t2} {rb} {y} (lam-stop x₁) (lam-stop x₂) = refl

Subst-not-found : ∀{r s t : Tm}{x : V} →
                  Subst r x s t →
                  varmem x (fvs s) ≡ ff →
                  s ≡ t
Subst-not-found {r} {var x} {t} {x} var-found m rewrite ≃-refl{x} with m
Subst-not-found {r} {var x} {t} {x} var-found m | ()
Subst-not-found {r} {var x₁} {t} {x} (var-not ne) m = refl
Subst-not-found {r} {s1 · s2} {t1 · t2} {x} (app sb1 sb2) m
  rewrite varmem-++ x (fvs s1) (fvs s2) | Subst-not-found{r}{s1}{t1}{x} sb1 (fst (||-≡-ff{varmem x (fvs s1)} m))
                                        | Subst-not-found{r}{s2}{t2}{x} sb2 (snd (||-≡-ff{varmem x (fvs s1)} m))
  = refl
Subst-not-found {r} {ƛ y s} {ƛ y t} {x} (lam-go x₂ x₃ sb) m with ∈ƛ{x}{y}{s} x₂
Subst-not-found {r} {ƛ y s} {ƛ y t} {x} (lam-go x₂ x₃ sb) m | p1 , _
 rewrite varmem-remove-neq{x}{y}{fvs s} p1 | Subst-not-found{r}{s}{t}{x} sb m = refl
Subst-not-found {r} {ƛ y s} {ƛ y t} {x} (lam-stop x₂) m = refl

Subst-refl : ∀{r s : Tm}{x : V} →
             varmem x (fvs s) ≡ ff →
             Subst r x s s
Subst-refl {r} {var y} {x} m = var-not (fst (||-≡-ff{x ≃ y} m))
Subst-refl {r} {s1 · s2} {x} m rewrite varmem-++ x (fvs s1) (fvs s2) =
  app (Subst-refl{r}{s1}{x} (fst (||-≡-ff{varmem x (fvs s1)} m)))
      (Subst-refl{r}{s2}{x} (snd (||-≡-ff{varmem x (fvs s1)} m)))
Subst-refl {r} {ƛ y s} {x} m = lam-stop m
