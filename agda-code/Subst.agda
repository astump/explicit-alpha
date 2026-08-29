open import lib
open import VarInterface

module Subst where

open import Tm 
open import Substitution 
open import Apart

data Subst : Tm → V → Tm → Tm → Set where
  var-found : ∀{t : Tm}{v : V} → 
              Subst t v (var v) t
  var-not : ∀{t : Tm}{v x : V} →
             v ≃ x ≡ ff → 
             Subst t v (var x) (var x)
  app : ∀{t : Tm}{v : V}
         {t1 t2 t1' t2' : Tm} → 
         Subst t v t1 t1' →
         Subst t v t2 t2' →
         Subst t v (t1 · t2) (t1' · t2')
  lam-go : ∀{t : Tm}{v : V}{x : V}{s s' : Tm} →
           v ∈ (ƛ x s) ≡ tt →
           x ∈ t ≡ ff →                 -- avoid capture
           Subst t v s s' →
           Subst t v (ƛ x s) (ƛ x s')
  lam-stop : ∀{t : Tm}{v : V}{x : V}{s : Tm} →
             v ∈ (ƛ x s) ≡ ff →
             Subst t v (ƛ x s) (ƛ x s)

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