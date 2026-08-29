open import lib
open import relations
open import VarInterface

module Beta where

open import Tm 
open import Subst 
open import Tau 

β : Rel Tm
β ((ƛ x t1) · t2) = Subst t2 x t1
β _ _ = ⊥

↝β : Rel Tm
↝β = τ β

{- deterministic-β : deterministic β
deterministic-β {(ƛ x t1) · t2} d1 d2  = substDeterministic d1 d2
-}

{- β preserves the set of bound variables -}
β-bvs : preserves-set β bvs _≃_
β-bvs{(ƛ x t1) · t2}{r} sb =
  varsub-trans {bvs r} {bvs t1 ++ bvs t2} {x :: bvs t1 ++ bvs t2}
    (varsub-trans {bvs r} {bvs t2 ++ bvs t1} {bvs t1 ++ bvs t2}
       (subst-bvs {t2} {t1} {r} {x} sb) (varsub-++-commute{bvs t2}{bvs t1})) (varsub-++2a{[ x ]}{bvs t1 ++ bvs t2})

↝β-bvs : preserves-set ↝β bvs _≃_
↝β-bvs {s} {t} (τ-base x) = β-bvs x
↝β-bvs {s1 · s2} {t1 · s2} (τ-app1 x) =
  varsub-++-merge {bvs t1} {bvs s1} {bvs s2} {bvs s2} (↝β-bvs{s1}{t1} x) (varsub-refl{bvs s2})
↝β-bvs {s1 · s2} {s1 · t2} (τ-app2 x) =
  varsub-++-merge {bvs s1} {bvs s1} {bvs t2} {bvs s2} (varsub-refl{bvs s1}) (↝β-bvs{s2}{t2} x)
↝β-bvs {ƛ y s} {ƛ y t} (τ-lam{x = y} x) = varsub-++-cong {[ y ]} {bvs t} {bvs s} ((↝β-bvs{s}{t} x))

↝β⋆-bvs : preserves-set (↝β ⋆) bvs _≃_
↝β⋆-bvs = preserves-⋆{B = V}{_≃_}{bvs} ≃-≡ (λ{x} → ≃-refl{x}) ↝β-bvs