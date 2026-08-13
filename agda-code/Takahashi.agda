{- The function proposed by Takahashi to compute the maximum
   parallel reduct of t.
-}
open import lib hiding (_>>=_ ; return ; _∘_)
open import relations
open import diamond
open import VarInterface
open import Monad

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

varsub-graft : ∀{x : V}{t1 t2 : Tm} →
               varsub (fvs (graft1 t2 x t1)) (varrem x (fvs t1) ++ fvs t2) ≡ tt
varsub-graft {x} {var y} {t} with keep (x ≃ y)
varsub-graft {x} {var y} {t} | tt , eq rewrite eq | ≃-sym{x} eq = isSublist-refl (λ{x} → ≃-refl{x}) {fvs t}
varsub-graft {x} {var y} {t} | ff , eq rewrite eq | ~≃-sym{x} eq | ≃-refl{y} = refl
varsub-graft {x} {t1 · t2} {t} = varsub-++il {fvs (graft [ x , t ] t1)}
                                  {fvs (graft [ x , t ] t2)}
                                  {varrem x (fvs t1 ++ fvs t2) ++ fvs t}
                                  (varsub-trans {fvs (graft [ x , t ] t1)}
                                    {varrem x (fvs t1) ++ fvs t}
                                    {varrem x (fvs t1 ++ fvs t2) ++ fvs t} 
                                    (varsub-graft{x}{t1}{t})
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
                                    (varsub-graft {x} {t2} {t})
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
varsub-graft {x} {ƛ y t1} {t} with keep (x ≃ y)
varsub-graft {x} {ƛ y t1} {t} | tt , eq rewrite eq | graft-[] {t1} | ≃-≡{x} eq | remove-idem{eq = _≃_}{y}{fvs t1} = varsub-++1{varrem y (fvs t1)}
varsub-graft {x} {ƛ y t1} {t} | ff , eq rewrite eq  =
  varsub-trans {varrem y (fvs (graft1 t x t1))}{varrem y (varrem x (fvs t1) ++ fvs t)}{varrem x (varrem y (fvs t1)) ++ fvs t}
    (varsub-remove-both {fvs (graft1 t x t1)}
      {varrem x (fvs t1) ++ fvs t} {y} (varsub-graft{x}{t1}{t})) h
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

varsub-fvs : ∀{t : Tm} → varsub (fvs (tk t)) (fvs t) ≡ tt
varsub-fvs{var x} rewrite ≃-refl{x} = refl
varsub-fvs{(var x) · t} = isSublist-++-cong{eq = _≃_}{[ x ]}{fvs (tk t)}{fvs t} (λ{x} → ≃-refl{x}) (varsub-fvs{t})
varsub-fvs{t1 · t2 · t3} = isSublist-++-merge {eq = _≃_} {fvs (tk (t1 · t2))} {fvs (t1 · t2)}
                            {fvs (tk t3)} {fvs t3} ≃-≡ (λ{x} → ≃-refl{x}) (varsub-fvs{t1 · t2}) (varsub-fvs{t3})
varsub-fvs{(ƛ x t1) · t2} = varsub-trans {fvs (graft1 (tk t2) x (tk t1))}
                             {varrem x (fvs (tk t1)) ++ fvs (tk t2)}
                             {varrem x (fvs t1) ++ fvs t2} (varsub-graft{x}{tk t1}{tk t2})
                             (varsub-++-merge {varrem x (fvs (tk t1))} {varrem x (fvs t1)}
                               {fvs (tk t2)} {fvs t2}
                               (varsub-remove-both {fvs (tk t1)} {fvs t1} {x} (varsub-fvs{t1}))
                               (varsub-fvs{t2}))
varsub-fvs{ƛ x t1} = varsub-remove-both {fvs (tk t1)} {fvs t1} {x} (varsub-fvs{t1})