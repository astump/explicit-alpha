-- 
{- The function proposed by Takahashi to compute the maximum
   parallel reduct of t.
-}
open import lib hiding (_>>=_ ; return ; _∘_)
open import relations
open import diamond
open import VarInterface

module Takahashi where

open import Tm 
open import Substitution
open import AlphaCanon

tk : Tm → Tm
tk (var x) = var x
tk (var x · t) = var x · tk t
tk ((t1 · t2) · t3) = (tk (t1 · t2)) · tk t3
tk ((ƛ x t1) · t2) = graft1 (tk t2) x (tk t1)
tk (ƛ x t) = ƛ x (tk t)

αtk : Tm → Renaming → Tm
αtk t ρ = tk (αc t ρ)

varsub-fvs-tk : ∀{t : Tm} → varsub (fvs (tk t)) (fvs t) ≡ tt
varsub-fvs-tk{var x} rewrite ≃-refl{x} = refl
varsub-fvs-tk{(var x) · t} = varsub-++-cong{[ x ]}{fvs (tk t)}{fvs t} (varsub-fvs-tk{t})
varsub-fvs-tk{t1 · t2 · t3} = varsub-++-merge {fvs (tk (t1 · t2))} {fvs (t1 · t2)}
                            {fvs (tk t3)} {fvs t3} (varsub-fvs-tk{t1 · t2}) (varsub-fvs-tk{t3})
varsub-fvs-tk{(ƛ x t1) · t2} = varsub-trans {fvs (graft1 (tk t2) x (tk t1))}
                             {varrem x (fvs (tk t1)) ++ fvs (tk t2)}
                             {varrem x (fvs t1) ++ fvs t2} (fvs-graft{x}{tk t1}{tk t2})
                             (varsub-++-merge {varrem x (fvs (tk t1))} {varrem x (fvs t1)}
                               {fvs (tk t2)} {fvs t2}
                               (varsub-remove-both {fvs (tk t1)} {fvs t1} {x} (varsub-fvs-tk{t1}))
                               (varsub-fvs-tk{t2}))
varsub-fvs-tk{ƛ x t1} = varsub-remove-both {fvs (tk t1)} {fvs t1} {x} (varsub-fvs-tk{t1})

varsub-bvs-tk : ∀{t : Tm} → varsub (bvs (tk t)) (bvs t) ≡ tt
varsub-bvs-tk{var x} = refl
varsub-bvs-tk{(var x) · t} = varsub-bvs-tk{t}
varsub-bvs-tk{t1 · t2 · t3}  = varsub-++-merge{bvs (tk (t1 · t2))}{bvs (t1 · t2)} (varsub-bvs-tk{t1 · t2}) (varsub-bvs-tk{t3})
varsub-bvs-tk{(ƛ x t1) · t2} = varsub-trans {bvs (graft1 (tk t2) x (tk t1))} {bvs t1 ++ bvs t2}
                             {x :: bvs t1 ++ bvs t2}
                             (varsub-trans {bvs (graft1 (tk t2) x (tk t1))}
                                {bvs (tk t1) ++ bvs (tk t2)} {bvs t1 ++ bvs t2}
                                (bvs-graft{x}{tk t1}{tk t2})
                                (varsub-++-merge {bvs (tk t1)} {bvs t1} {bvs (tk t2)} {bvs t2}
                                  (varsub-bvs-tk{t1}) (varsub-bvs-tk{t2})))
                             (varsub-++2a{[ x ]}{bvs t1 ++ bvs t2})
varsub-bvs-tk{ƛ x t1} = varsub-++-cong{[ x ]}{bvs (tk t1)}{bvs t1} (varsub-bvs-tk{t1})

-- a related function, for computing the superdevelopment of t
sd : Tm → Tm
sd (var x) = var x
sd (t1 · t2) with sd t1
sd (t1 · t2) | ƛ x t1' = graft1 (sd t2) x t1'
sd (t1 · t2) | var x = var x · (sd t2)
sd (t1 · t2) | ta · tb = ta · tb · (sd t2)
sd (ƛ x t) = ƛ x (sd t)

varsub-fvs-sd : ∀{t : Tm} → varsub (fvs (sd t)) (fvs t) ≡ tt
varsub-fvs-sd {var x} = varsub-refl{[ x ]}
varsub-fvs-sd {t1 · t2} with keep (sd t1) | varsub-fvs-sd{t1} | varsub-fvs-sd{t2}
varsub-fvs-sd {t1 · t2} | ƛ x t1' , eq | d1 | d2 rewrite eq =
  varsub-trans {fvs (graft1 (sd t2) x t1')}
               {varrem x (fvs t1') ++ fvs (sd t2)}
               {fvs t1 ++ fvs t2}
     (fvs-graft{x}{t1'}{sd t2})
     (varsub-++-merge {varrem x (fvs t1')} {fvs t1} {fvs (sd t2)} {fvs t2}
       (h eq)
       (varsub-fvs-sd{t2}))
  where h : ∀ {t : Tm} → sd t1 ≡ t → varsub (fvs t) (fvs t1) ≡ tt
        h {t} refl = varsub-fvs-sd{t1}
varsub-fvs-sd {t1 · t2} | var x , eq | d1 | d2 rewrite eq | &&-tt (varmem x (fvs t1)) | varmem-++ x (fvs t1)(fvs t2) =
 &&-intro {varmem x (fvs t1) || varmem x (fvs t2)} (||-intro1 d1) (varsub-++2 {fvs t1} {fvs (sd t2)} {fvs t2} d2)
varsub-fvs-sd {t1 · t2} | ta · tb , eq | d1 | d2 rewrite eq =
 varsub-++-merge{fvs ta ++ fvs tb}{fvs t1}{fvs (sd t2)}{fvs t2} d1 d2
varsub-fvs-sd {ƛ x t} = varsub-remove-both {fvs (sd t)} {fvs t} {x} (varsub-fvs-sd{t})

varsub-bvs-sd : ∀{t : Tm} → varsub (bvs (sd t)) (bvs t) ≡ tt
varsub-bvs-sd {var x} = refl
varsub-bvs-sd {t1 · t2} with keep (sd t1)
varsub-bvs-sd {t1 · t2} | var x , eq rewrite eq = varsub-++2 {bvs t1} {bvs (sd t2)} {bvs t2} (varsub-bvs-sd{t2})
varsub-bvs-sd {t1 · t2} | ƛ x t1' , eq rewrite eq =
  varsub-trans {bvs (graft1 (sd t2) x t1')} {bvs t1' ++ bvs (sd t2)} {bvs t1 ++ bvs t2}
    (bvs-graft {x} {t1'} {sd t2})
    (varsub-++-merge {bvs t1'} {bvs t1} {bvs (sd t2)} {bvs t2}
      h
      (varsub-bvs-sd{t2}))
   where h : varsub (bvs t1') (bvs t1) ≡ tt
         h with varsub-bvs-sd{t1}
         h | p rewrite eq = varsub-++2l {[ x ]} {bvs t1'} {bvs t1} p
varsub-bvs-sd {t1 · t2} | ta · tb , eq rewrite eq with varsub-bvs-sd{t1}
varsub-bvs-sd {t1 · t2} | ta · tb , eq | p rewrite eq = 
  varsub-++-merge {bvs ta ++ bvs tb} {bvs t1} {bvs (sd t2)} {bvs t2}
    p
    (varsub-bvs-sd{t2})
varsub-bvs-sd {ƛ x t} = varsub-++-cong {[ x ]} {bvs (sd t)} {bvs t} (varsub-bvs-sd{t})