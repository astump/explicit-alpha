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

varsub-fvs : ∀{t : Tm} → varsub (fvs (tk t)) (fvs t) ≡ tt
varsub-fvs{var x} rewrite ≃-refl{x} = refl
varsub-fvs{(var x) · t} = isSublist-++-cong{eq = _≃_}{[ x ]}{fvs (tk t)}{fvs t} (λ{x} → ≃-refl{x}) (varsub-fvs{t})
varsub-fvs{t1 · t2 · t3} = varsub-++-merge {fvs (tk (t1 · t2))} {fvs (t1 · t2)}
                            {fvs (tk t3)} {fvs t3} (varsub-fvs{t1 · t2}) (varsub-fvs{t3})
varsub-fvs{(ƛ x t1) · t2} = varsub-trans {fvs (graft1 (tk t2) x (tk t1))}
                             {varrem x (fvs (tk t1)) ++ fvs (tk t2)}
                             {varrem x (fvs t1) ++ fvs t2} (fvs-graft{x}{tk t1}{tk t2})
                             (varsub-++-merge {varrem x (fvs (tk t1))} {varrem x (fvs t1)}
                               {fvs (tk t2)} {fvs t2}
                               (varsub-remove-both {fvs (tk t1)} {fvs t1} {x} (varsub-fvs{t1}))
                               (varsub-fvs{t2}))
varsub-fvs{ƛ x t1} = varsub-remove-both {fvs (tk t1)} {fvs t1} {x} (varsub-fvs{t1})

varsub-bvs : ∀{t : Tm} → varsub (bvs (tk t)) (bvs t) ≡ tt
varsub-bvs{var x} = refl
varsub-bvs{(var x) · t} = varsub-bvs{t}
varsub-bvs{t1 · t2 · t3}  = varsub-++-merge{bvs (tk (t1 · t2))}{bvs (t1 · t2)} (varsub-bvs{t1 · t2}) (varsub-bvs{t3})
varsub-bvs{(ƛ x t1) · t2} = varsub-trans {bvs (graft1 (tk t2) x (tk t1))} {bvs t1 ++ bvs t2}
                             {x :: bvs t1 ++ bvs t2}
                             (varsub-trans {bvs (graft1 (tk t2) x (tk t1))}
                                {bvs (tk t1) ++ bvs (tk t2)} {bvs t1 ++ bvs t2}
                                (bvs-graft{x}{tk t1}{tk t2})
                                (varsub-++-merge {bvs (tk t1)} {bvs t1} {bvs (tk t2)} {bvs t2}
                                  (varsub-bvs{t1}) (varsub-bvs{t2})))
                             (varsub-++2a{[ x ]}{bvs t1 ++ bvs t2})
varsub-bvs{ƛ x t1} = varsub-++-cong{[ x ]}{bvs (tk t1)}{bvs t1} (varsub-bvs{t1})
