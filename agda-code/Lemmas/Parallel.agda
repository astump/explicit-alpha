open import lib
open import relations
open import VarInterface
open import VarImpls

module Lemmas.Parallel(vi : VI) where

open VI VI-𝕃𝔹

open import Tm VI-𝕃𝔹
open import Subst VI-𝕃𝔹
open import Substitution VI-𝕃𝔹
open import Apart VI-𝕃𝔹
open import VarOps VI-𝕃𝔹
open import Fresh
open import AlphaCanon 
open import Beta VI-𝕃𝔹
open import Tau VI-𝕃𝔹
open import Parallel VI-𝕃𝔹
open import Renaming VI-𝕃𝔹
open import Takahashi 

open import Lemmas.VarOps VI-𝕃𝔹
open import Lemmas.Tm VI-𝕃𝔹
open import Lemmas.Beta VI-𝕃𝔹
open import Lemmas.Tau VI-𝕃𝔹
open import Lemmas.VarInterface VI-𝕃𝔹
open import Lemmas.Apart VI-𝕃𝔹
open import Lemmas.AlphaCanon 
open import Lemmas.Takahashi 
open import Lemmas.Fresh
open import Lemmas.Renaming VI-𝕃𝔹
open import Lemmas.Substitution VI-𝕃𝔹
open import Lemmas.Subst VI-𝕃𝔹


-- parallel reduction without alpha is reflexive
⇒αβ-refl : ∀{t : Tm} → t ⟨ ⇒αβ tt ⟩ t
⇒αβ-refl {var x} = var
⇒αβ-refl {t · t₁} = app ⇒αβ-refl ⇒αβ-refl
⇒αβ-refl {ƛ x t} = lam ⇒αβ-refl


⇒αβ-relax : ∀{s t : Tm}{b : 𝔹} →
            b ≡ tt → 
            s ⟨ ⇒αβ b ⟩ t →
            s ⟨ ⇒αβ ff ⟩ t 
⇒αβ-relax {var x} {t} u var = var
⇒αβ-relax {s1 · s2} {t1 · t2} u (app{b1 = b1}{b2} x x₁) =
 app {s1}{b1 = ff}{ff}
   (⇒αβ-relax {s1} {t1} {b1} (&&-elim1 u) x)
   (⇒αβ-relax {s2} {t2} {b2} (&&-elim2 u) x₁)
⇒αβ-relax {s1 · s2} {t} u (beta{t1}{v}{t2}{t1'}{t2'}{t}{b1}{b2} x x₁ x₂) =
 beta {x = v}{t1' = t1'}{t2'}{t} {ff} {ff}
  (⇒αβ-relax{s2}{t1'} (&&-elim1 u) x) (⇒αβ-relax {t2} {t2'} (&&-elim2 u) x₁)
  x₂
⇒αβ-relax {ƛ x s} {ƛ x t} u (lam x₁) = lam (⇒αβ-relax{s}{t} u x₁)


⇒αβ-relax' : ∀{s t : Tm}{b : 𝔹} →
             s ⟨ ⇒αβ b ⟩ t →
             s ⟨ ⇒αβ ff ⟩ t 
⇒αβ-relax'{s}{t}{tt} = ⇒αβ-relax{s}{t}{tt} refl
⇒αβ-relax'{s}{t}{ff} d = d


{- parallel reduction without alpha-step implies multi-step beta-reduction -}
⇒αβ-β : ∀{s t : Tm}{b : 𝔹} →
         b ≡ tt → 
         s ⟨ ⇒αβ b ⟩ t →
         s ⟨ ↝β ⋆ ⟩ t
⇒αβ-β {var x} {var _} be var = ⋆refl
⇒αβ-β {(ƛ x s1) · s2} {t} be (beta d1 d2 sb) = 
  ⋆app1 (⋆lam{x} (⇒αβ-β{s1} (&&-elim2 be) d2)) ⋆trans
  ⋆app2 (⇒αβ-β{s2} (&&-elim1 be) d1) ⋆trans
  ⋆base (τ-base sb)

⇒αβ-β {s1 · s2} {t1 · t2} be (app d1 d2) =
  ⋆app1 (⇒αβ-β{s1} (&&-elim1 be) d1) ⋆trans
  ⋆app2 (⇒αβ-β{s2} (&&-elim2 be) d2)
⇒αβ-β {ƛ x s} {ƛ x₁ t} be (lam d) = ⋆lam (⇒αβ-β{s} be d)

-- parallel reduction preserves the set of bound variables
⇒αβ-bvs : preserves-set (⇒αβ tt) bvs _≃_
⇒αβ-bvs d = ↝β⋆-bvs (⇒αβ-β refl d) 


{- Terms that are path distinct with respect to a set vs
   reduce to their complete developments, without alpha steps -}
PathDistinct-tk : ∀{t : Tm}{vs : 𝕃 V} →
           PathDistinct vs t →
           t ⟨ ⇒αβ tt ⟩ (tk t)
PathDistinct-tk{var x}{vs} pd = var
PathDistinct-tk{var x · t}{vs} (app _ pd2) = app var (PathDistinct-tk{t}{vs} pd2)
PathDistinct-tk{t1 · t2 · t3}{vs} (app pd1 pd2) =
 app (PathDistinct-tk{t1 · t2}{vs} pd1)
     (PathDistinct-tk{t3}{vs} pd2)
PathDistinct-tk{(ƛ x t1) · t2}{vs} (app (lam u pd1) pd2)  =
   beta {t2} {x} {t1} {tk t2} {tk t1} {graft1 (tk t2) x (tk t1)} {tt} {tt}
    (PathDistinct-tk {t2} {vs}
      pd2)
    (PathDistinct-tk {t1} {x :: vs} 
        pd1)
    (substLem (varapart-varsub {bvs (tk t1)} {bvs t1} {fvs (tk t2)} {fvs t2}
                (varsub-bvs-tk{t1}) (varsub-fvs-tk{t2})
                 (varapart-sym {fvs t2} {bvs t1}
                  (PathDistinct-Apart'{t1}{fvs t2}{x :: vs} pd1 h))))
 where h : varsub (fvs t2) (x :: vs) ≡ tt                  
       h = varsub-++2 {[ x ]} {fvs t2} {vs} (PathDistinct-fvs{t2}{vs} pd2)
PathDistinct-tk{ƛ x t}{vs} (lam u pd) =
 lam (PathDistinct-tk {t} {x :: vs} pd)


{--------------------------------------------------------------------------------
 - Main theorem 1:

   Any term's α-canonization can be completely developed, without alpha-steps.
 -
 --------------------------------------------------------------------------------}
⇒αtk : ∀{t : Tm} →
       let a = αcanon t in
        a ⟨ ⇒αβ tt ⟩ tk a 
⇒αtk{t} = PathDistinct-tk (PathDistinct-αc{t} h h3)
 where vs : 𝕃 V
       vs = fvs t
       h : varsub vs (domr (diagonal (vs))) ≡ tt
       h rewrite domr-diag{vs} = varsub-refl{vs}
       hi : varsub (vs) (domr (diagonal (vs))) ≡ tt
       hi rewrite domr-diag{vs} = varsub-refl{vs}
       h2 : varsub (fvs (αcanon t)) (ranr (diagonal (vs))) ≡ tt
       h2 with fvs-αc{t}{fresh vs}{diagonal vs} hi 
       h2 | u rewrite ranr-diag{vs} = u
       h3 : Ubounded (ranr (diagonal (fvs t))) (fresh (fvs t))
       h3 rewrite ranr-diag{fvs t} = Ubounded-fresh{fvs t}

{-
{--------------------------------------------------------------------------------
- Corollary

  The alpha-canonization of t reduces with beta-steps to its complete development.
-
--------------------------------------------------------------------------------}
↝β-αtk : ∀{t : Tm} →
         let a = αcanon t in
         a ⟨ ↝β ⋆ ⟩ tk a
↝β-αtk{t} = ⇒αβ-β refl (⇒αtk{t})

↝β-tk : ∀{t : Tm}{vs : 𝕃 V} →
         varsub (fvs t) vs ≡ tt → 
         PathDistinct vs t ≡ tt →
         t ⟨ ↝β ⋆ ⟩ tk t
↝β-tk{t}{vs} sb di = ⇒αβ-β refl (PathDistinct-tk{t}{vs} di)


{- If

      - all variables of s are distinct, and
      - s parallel reduces to t without alpha

   then

      - t is path distinct: no nested bindings of the same variable, and
                            the bound vars are distinct from the free ones.
-}   
⇒αβ-all-to-path : ∀{s t : Tm}{b : 𝔹}{vs : 𝕃 V} →
                  b ≡ tt →   -- no alpha steps
                  allDistinct vs s ≡ tt →
                  s ⟨ ⇒αβ b ⟩ t → 
                  PathDistinct vs t ≡ tt 
⇒αβ-all-to-path {var x} {var _}{_}{vs} _ ad var = all-to-path {var x}{vs} ad
⇒αβ-all-to-path {s1 · s2} {t1 · t2}{_}{vs} beq ad (app{b1 = b1}{b2} d1 d2)
  rewrite ⇒αβ-all-to-path{s1}{t1}{b1}{vs} (&&-elim1 beq) (allDistinct-app1{s1}{s2}{vs} ad) d1 =
  ⇒αβ-all-to-path{s2}{t2}{b2}{vs} (&&-elim2 beq) (allDistinct-app2{s1}{s2}{vs} ad) d2
⇒αβ-all-to-path {(ƛ x s1) · s2} {t}{_}{vs} beq ad (beta{x = x}{t1' = t2'}{t1'}{b1 = b1}{b2} d1 d2 sb) rewrite &&-elim1{b1} beq | &&-elim2{b1} beq =
  PathDistinct-Subst {t2'} {t1'} {t} {x} {[]} {vs}
    (⇒αβ-all-to-path {s2} {t2'} {tt} {vs} refl (allDistinct-app2{ƛ x s1}{s2}{vs} ad) d1)
    ((⇒αβ-all-to-path {s1} {t1'} {tt} {x :: vs} refl
      (snd (allDistinct-lam{x}{s1}{vs} (allDistinct-app1{ƛ x s1}{s2}{vs} ad))) d2))
    (varapart-varsub {bvs t2'} {bvs s2} {bvs t1'} {bvs s1} (⇒αβ-bvs d1)
      (⇒αβ-bvs{s1}{t1'} d2)
      (varapart-sym {bvs s1} {bvs s2}
        (varunique-++-varapart {bvs s1} {bvs s2}
          (&&-elim2{~ varmem x (bvs s1 ++ bvs s2)} (&&-elim1 ad)))))
    sb

⇒αβ-all-to-path {ƛ x s} {ƛ y t}{_}{vs} beq ad (lam d) with allDistinct-lam{x}{s}{vs} ad 
⇒αβ-all-to-path {ƛ x s} {ƛ y t}{b}{vs} beq ad (lam d) | vm , ad' rewrite vm =
  ⇒αβ-all-to-path {s} {t} {b} {x :: vs} beq ad' d

{----------------------------------------------------------------------
 - Another main theorem

 If all variables are distinct, then you can completely develop a
 term twice, without alpha
 ----------------------------------------------------------------------}
↝β-tk2 : ∀{t : Tm} →
         allDistinct (fvs t) t ≡ tt →
         t ⟨ ↝β ⋆ ⟩ tk (tk t)
↝β-tk2{t} ad = ↝β-tk {t} {fvs t} (varsub-refl{fvs t}) (all-to-path{t} ad)
               ⋆trans
               ↝β-tk {tk t} {fvs t} (varsub-fvs-tk{t})
                 (⇒αβ-all-to-path {t} {tk t} {tt} {fvs t} refl ad
                   (PathDistinct-tk{t}{fvs t} (all-to-path{t} ad)))

-}