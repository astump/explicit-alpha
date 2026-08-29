{- definition of parallel reduction
-}
open import lib
open import relations
open import VarInterface

module Parallel where

open import Beta
open import Tau 
open import Tm 
open import Subst
open import Apart
open import Renaming
open import AlphaCanon
open import Takahashi 

{- parallel reduction, including both alpha- and beta-steps.

   The boolean tells whether or not this is alpha-free -}
data ⇒αβ : 𝔹 → Tm → Tm → Set where
  var : ∀{v : V} → 
          var v ⟨ ⇒αβ tt ⟩ var v
  app : ∀{t1 t2 t1' t2' : Tm}{b1 b2 : 𝔹} →
        t1 ⟨ ⇒αβ b1 ⟩ t1' →
        t2 ⟨ ⇒αβ b2 ⟩ t2' →
        t1 · t2 ⟨ ⇒αβ (b1 && b2) ⟩ t1' · t2'
  beta : ∀{t1 : Tm}{x : V}{t2 : Tm}{t1' t2' r : Tm}{b1 b2 : 𝔹} →
         t1 ⟨ ⇒αβ b1 ⟩ t1' →
         t2 ⟨ ⇒αβ b2 ⟩ (ƛ x t2') →        
         Subst t1' x t2' r → 
         t2 · t1 ⟨ ⇒αβ (b1 && b2) ⟩ r
  alpha : ∀{x x' : V}{t t' r : Tm}{b : 𝔹} →
          x' ∈ t' ≡ ff →                              -- avoid capture
          x ≃ x' ≡ ff → 
          t ⟨ ⇒αβ b ⟩ t' →
          Subst (var x') x t' r → 
          (ƛ x t) ⟨ ⇒αβ ff ⟩ (ƛ x' r)
  lam : ∀{t t' : Tm}{x : V}{b : 𝔹} →
        t ⟨ ⇒αβ b ⟩ t' →
        ƛ x t ⟨ ⇒αβ b ⟩ ƛ x t'

-- parallel reduction without alpha is reflexive
⇒αβ-refl : ∀{t : Tm} → t ⟨ ⇒αβ tt ⟩ t
⇒αβ-refl {var x} = var
⇒αβ-refl {t · t₁} = app ⇒αβ-refl ⇒αβ-refl
⇒αβ-refl {ƛ x t} = lam ⇒αβ-refl

{- parallel reduction without alpha-step implies multi-step beta-reduction -}
⇒αβ-β : ∀{s t : Tm}{b : 𝔹} →
         b ≡ tt → 
         s ⟨ ⇒αβ b ⟩ t →
         s ⟨ ↝β ⋆ ⟩ t
⇒αβ-β {var x} {var _} be var = ⋆refl
⇒αβ-β {s1 · s2} {t} be (beta d1 d2 sb) =
  ⋆app1 (⇒αβ-β{s1} (&&-elim2 be) d2) ⋆trans
  ⋆app2 (⇒αβ-β{s2} (&&-elim1 be) d1) ⋆trans
  ⋆base (τ-base sb)
⇒αβ-β {s1 · s2} {t1 · t2} be (app d1 d2) =
  ⋆app1 (⇒αβ-β{s1} (&&-elim1 be) d1) ⋆trans
  ⋆app2 (⇒αβ-β{s2} (&&-elim2 be) d2)
⇒αβ-β {ƛ x s} {ƛ x₁ t} be (lam d) = ⋆lam (⇒αβ-β{s} be d)

-- parallel reduction preserves the set of bound variables
⇒αβ-bvs : preserves-set (⇒αβ tt) bvs _≃_
⇒αβ-bvs d = ↝β⋆-bvs (⇒αβ-β refl d) 

{- Terms that are path distinct with respect to a set vs including the free variables of t
   parallel reduce to their complete developments, without alpha steps -}
pathDistinct-tk : ∀{t : Tm}{vs : 𝕃 V} →
           varsub (fvs t) vs ≡ tt → 
           pathDistinct vs t ≡ tt →
           t ⟨ ⇒αβ tt ⟩ (tk t)
pathDistinct-tk{var x}{vs} sub ok = var
pathDistinct-tk{var x · t}{vs} sub ok = app var (pathDistinct-tk{t}{vs} (isSublist-++2l{eq = _≃_}{[ x ]}{fvs t}{vs} sub) (&&-elim2 ok))
pathDistinct-tk{t1 · t2 · t3}{vs} sub ok =
 app (pathDistinct-tk{t1 · t2}{vs} (isSublist-++1l{eq = _≃_}{fvs t1 ++ fvs t2}{fvs t3}{vs} sub) (&&-elim1 ok))
     (pathDistinct-tk{t3}{vs} ((isSublist-++2l{eq = _≃_}{fvs t1 ++ fvs t2}{fvs t3}{vs} sub)) (&&-elim2 ok))
pathDistinct-tk{(ƛ x t1) · t2}{vs} sub ok =
  beta {t2} {x} {ƛ x t1} {tk t2} {tk t1}{b1 = tt}{tt}
   (pathDistinct-tk {t2} {vs} (isSublist-++2l{eq = _≃_}{remove _≃_ x (fvs t1)}{fvs t2}{vs} sub)
       (&&-elim2 ok))
   (lam (pathDistinct-tk {t1} {x :: vs}
      (isSublist-remove{eq = _≃_}{fvs t1}{vs}{x} (λ{x} → ≃-sym{x})
        ((isSublist-++1l{eq = _≃_}{remove _≃_ x (fvs t1)}{fvs t2}{vs} sub)))
      (&&-elim2{~ varmem x vs} (&&-elim1 ok))))
   (substLem (varapart-varsub {bvs (tk t1)} {bvs t1} {fvs (tk t2)} {fvs t2}
                (varsub-bvs-tk{t1}) (varsub-fvs-tk{t2})
                 (varapart-sym {fvs t2} {bvs t1}
                  (pathDistinct-Apart'{t1}{fvs t2}{x :: vs} (&&-elim2{~ varmem x vs} (&&-elim1 ok)) h))))
 where h : varsub (fvs t2) (x :: vs) ≡ tt                  
       h rewrite varsub-++{varrem x (fvs t1)}{fvs t2}{vs} =
         varsub-trans {fvs t2} {vs} {x :: vs} (&&-elim2 sub) (varsub-++2a{[ x ]}{vs})
pathDistinct-tk{ƛ x t}{vs} sub ok =
 lam (pathDistinct-tk {t} {x :: vs} (isSublist-remove{eq = _≃_}{fvs t}{vs}{x} (λ{x} → ≃-sym{x}) sub) (&&-elim2 ok))

{--------------------------------------------------------------------------------
 - Main theorem 1:

   Any term's α-canonization can be completely developed, without alpha-steps.
 -
 --------------------------------------------------------------------------------}
⇒αtk : ∀{t : Tm} →
       let a = αcanon t in
        a ⟨ ⇒αβ tt ⟩ tk a 
⇒αtk{t} = pathDistinct-tk h2 (αc-pathDistinct{t} h)
 where h : varsub (fvs t) (domr (diagonal (fvs t))) ≡ tt
       h rewrite domr-diag{fvs t} = varsub-refl{fvs t}
       hi : varsub (fvs t) (domr (diagonal (fvs t))) ≡ tt
       hi rewrite domr-diag{fvs t} = varsub-refl{fvs t}
       h2 : varsub (fvs (αcanon t)) (ranr (diagonal (fvs t))) ≡ tt
       h2 with fvs-αc{t}{diagonal (fvs t)} hi 
       h2 | u rewrite ranr-diag{fvs t} = u

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
         pathDistinct vs t ≡ tt →
         t ⟨ ↝β ⋆ ⟩ tk t
↝β-tk{t}{vs} sb di = ⇒αβ-β refl (pathDistinct-tk{t}{vs} sb di)

{- Terms that are path distinct with respect to a set vs including the free variables of t
   parallel reduce to their complete superdevelopments, without alpha steps -}
pathDistinct-sd : ∀{t : Tm}{vs : 𝕃 V} →
           varsub (fvs t) vs ≡ tt → 
           pathDistinct vs t ≡ tt →
           t ⟨ ⇒αβ tt ⟩ (sd t)
pathDistinct-sd {var x} {vs} sub ok = var
pathDistinct-sd {t1 · t2} {vs} sub ok
 with keep (sd t1)
    | (pathDistinct-sd{t1}{vs} (varsub-++1l{fvs t1}{fvs t2}{vs} sub) (&&-elim1 ok)) 
    | (pathDistinct-sd{t2}{vs} (varsub-++2l{fvs t1}{fvs t2}{vs} sub) (&&-elim2 ok))
pathDistinct-sd {t1 · t2} {vs} sub ok | ƛ x t1' , eq | d1 | d2 rewrite eq =
  beta{t2}{x}{t1}{sd t2}{t1'}{b1 = tt}{tt}
    (pathDistinct-sd {t2} {vs} (varsub-++2l{fvs t1}{fvs t2}{vs} sub) (&&-elim2 ok)) d1
   (substLem
      (varapart-varsub {bvs t1'} {bvs t1} {fvs (sd t2)} {fvs t2}
        h1
        (varsub-fvs-sd{t2})
        (varapart-sym {fvs t2} {bvs t1}
          (pathDistinct-Apart' {t1} {fvs t2} {vs}
            (&&-elim1 ok) (varsub-++2l{fvs t1}{fvs t2}{vs} sub)))))
 where h1 : varsub (bvs t1') (bvs t1) ≡ tt
       h1 with varsub-bvs-sd{t1} 
       h1 | q rewrite eq = &&-elim2 q
pathDistinct-sd {t1 · t2} {vs} sub ok | var x , eq | d1 | d2 rewrite eq | sym eq = app d1 d2
pathDistinct-sd {t1 · t2} {vs} sub ok | ta · tb , eq | d1 | d2 rewrite eq | sym eq = app d1 d2
pathDistinct-sd {ƛ x t} {vs} sub ok =
 lam (pathDistinct-sd {t} {x :: vs} (isSublist-remove{eq = _≃_}{fvs t}{vs}{x} (λ{x} → ≃-sym{x}) sub) (&&-elim2 ok))

{--------------------------------------------------------------------------------
 - Improved version of main theorem 1:

   Any term's α-canonization can be supercompletely developed, without alpha-steps.

   This version uses superdevelopments instead of developments.
 -
 --------------------------------------------------------------------------------}
⇒αsd : ∀{t : Tm} →
       let a = αcanon t in
        a ⟨ ⇒αβ tt ⟩ sd a 
⇒αsd{t} = pathDistinct-sd h2 (αc-pathDistinct{t} h)
 where h : varsub (fvs t) (domr (diagonal (fvs t))) ≡ tt
       h rewrite domr-diag{fvs t} = varsub-refl{fvs t}
       hi : varsub (fvs t) (domr (diagonal (fvs t))) ≡ tt
       hi rewrite domr-diag{fvs t} = varsub-refl{fvs t}
       h2 : varsub (fvs (αcanon t)) (ranr (diagonal (fvs t))) ≡ tt
       h2 with fvs-αc{t}{diagonal (fvs t)} hi 
       h2 | u rewrite ranr-diag{fvs t} = u

{--------------------------------------------------------------------------------
- Corollary

  The alpha-canonization of t reduces with beta-steps to its complete superdevelopment.
-
--------------------------------------------------------------------------------}
↝β-αsd : ∀{t : Tm} →
         let a = αcanon t in
         a ⟨ ↝β ⋆ ⟩ sd a
↝β-αsd{t} = ⇒αβ-β refl (⇒αsd{t})

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
                  pathDistinct vs t ≡ tt 
⇒αβ-all-to-path {var x} {var _}{_}{vs} _ ad var = all-to-path {var x}{vs} ad
⇒αβ-all-to-path {s1 · s2} {t1 · t2}{_}{vs} beq ad (app{b1 = b1}{b2} d1 d2)
  rewrite ⇒αβ-all-to-path{s1}{t1}{b1}{vs} (&&-elim1 beq) (allDistinct-app1{s1}{s2}{vs} ad) d1 =
  ⇒αβ-all-to-path{s2}{t2}{b2}{vs} (&&-elim2 beq) (allDistinct-app2{s1}{s2}{vs} ad) d2
⇒αβ-all-to-path {s1 · s2} {t}{_}{vs} beq ad (beta{x = x}{t1' = t2'}{t1'}{b1 = b1}{b2} d1 d2 sb) rewrite &&-elim1{b1} beq | &&-elim2{b1} beq =
 pathDistinct-Subst {t2'} {t1'} {t} {x} {[]}{vs}
  (⇒αβ-all-to-path {s2} {t2'} {tt} {vs} refl (allDistinct-app2{s1}{s2}{vs} ad) d1)
  (&&-elim2{~ varmem x vs} (⇒αβ-all-to-path {s1} {ƛ x t1'} {tt} {vs} refl (allDistinct-app1{s1}{s2}{vs} ad) d2))
  (varapart-varsub {bvs t2'} {bvs s2} {bvs t1'} {bvs s1} (⇒αβ-bvs d1)
    (varsub-trans {bvs t1'} {x :: bvs t1'} {bvs s1} (varsub-++2a{[ x ]}{bvs t1'}) (⇒αβ-bvs d2))
    (varapart-sym {bvs s1} {bvs s2}
      (varunique-++-varapart {bvs s1} {bvs s2} (&&-elim1 ad))))
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
               ⋆trans ↝β-tk {tk t} {fvs t} (varsub-fvs-tk{t})
                        (⇒αβ-all-to-path {t} {tk t} {tt} {fvs t} refl ad
                          (pathDistinct-tk{t}{fvs t} (varsub-refl{fvs t}) (all-to-path{t} ad)))