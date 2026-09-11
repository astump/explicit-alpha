{- more liberal definition of parallel reduction, corresponding to superdevelopments.
-}
open import lib
open import relations
open import VarInterface

module ParallelPlus where

open import Beta
open import Tau 
open import Tm 
open import Subst
open import Apart
open import Renaming
open import AlphaCanon
open import Takahashi 

{- parallel reduction, including both alpha- and beta-steps.
   The beta case is more liberal than for ⇒αβ of Parallel.agda.

   The boolean tells whether or not this is alpha-free -}
data ⇒αβ₊ : 𝔹 → Tm → Tm → Set where
  var : ∀{v : V}{b : 𝔹} → 
          var v ⟨ ⇒αβ₊ b ⟩ var v
  app : ∀{t1 t2 t1' t2' : Tm}{b1 b2 : 𝔹} →
        t1 ⟨ ⇒αβ₊ b1 ⟩ t1' →
        t2 ⟨ ⇒αβ₊ b2 ⟩ t2' →
        t1 · t2 ⟨ ⇒αβ₊ (b1 && b2) ⟩ t1' · t2'
  beta : ∀{t1 : Tm}{x : V}{t2 : Tm}{t1' t2' r : Tm}{b1 b2 : 𝔹} →
         t1 ⟨ ⇒αβ₊ b1 ⟩ t1' →
         t2 ⟨ ⇒αβ₊ b2 ⟩ (ƛ x t2') →        
         Subst t1' x t2' r → 
         t2 · t1 ⟨ ⇒αβ₊ (b1 && b2) ⟩ r
  alpha : ∀{x x' : V}{t t' r : Tm}{b : 𝔹} →
          x' ∈ t' ≡ ff →                              -- avoid capture
          x ≃ x' ≡ ff → 
          t ⟨ ⇒αβ₊ b ⟩ t' →
          Subst (var x') x t' r → 
          (ƛ x t) ⟨ ⇒αβ₊ ff ⟩ (ƛ x' r)
  lam : ∀{t t' : Tm}{x : V}{b : 𝔹} →
        t ⟨ ⇒αβ₊ b ⟩ t' →
        ƛ x t ⟨ ⇒αβ₊ b ⟩ ƛ x t'

-- parallel reduction without alpha is reflexive
⇒αβ₊-refl : ∀{t : Tm} → t ⟨ ⇒αβ₊ tt ⟩ t
⇒αβ₊-refl {var x} = var
⇒αβ₊-refl {t · t₁} = app ⇒αβ₊-refl ⇒αβ₊-refl
⇒αβ₊-refl {ƛ x t} = lam ⇒αβ₊-refl

⇒αβ₊-relax : ∀{s t : Tm}{b : 𝔹} →
            b ≡ tt → 
            s ⟨ ⇒αβ₊ b ⟩ t →
            s ⟨ ⇒αβ₊ ff ⟩ t 
⇒αβ₊-relax {var x} {t} u var = var
⇒αβ₊-relax {s1 · s2} {t1 · t2} u (app{b1 = b1}{b2} x x₁) =
 app {s1}{b1 = ff}{ff}
   (⇒αβ₊-relax {s1} {t1} {b1} (&&-elim1 u) x)
   (⇒αβ₊-relax {s2} {t2} {b2} (&&-elim2 u) x₁)
⇒αβ₊-relax {s1 · s2} {t} u (beta{x = v}{t1' = t1'}{t2'}{t}{b1}{b2} x x₁ x₂) =
 beta {x = v}{t1' = t1'}{t2'}{t} {ff} {ff}
  (⇒αβ₊-relax{s2}{t1'} (&&-elim1 u) x) (⇒αβ₊-relax{s1}{ƛ v t2'} (&&-elim2 u) x₁)
  x₂
⇒αβ₊-relax {ƛ x s} {ƛ x t} u (lam x₁) = lam (⇒αβ₊-relax{s}{t} u x₁)

⇒αβ₊-relax' : ∀{s t : Tm}{b : 𝔹} →
             s ⟨ ⇒αβ₊ b ⟩ t →
             s ⟨ ⇒αβ₊ ff ⟩ t 
⇒αβ₊-relax'{s}{t}{tt} = ⇒αβ₊-relax{s}{t}{tt} refl
⇒αβ₊-relax'{s}{t}{ff} d = d

{- parallel reduction without alpha-step implies multi-step beta-reduction -}
⇒αβ₊-β : ∀{s t : Tm}{b : 𝔹} →
         b ≡ tt → 
         s ⟨ ⇒αβ₊ b ⟩ t →
         s ⟨ ↝β ⋆ ⟩ t
⇒αβ₊-β {var x} {var _} be var = ⋆refl
⇒αβ₊-β {s1 · s2} {t} be (beta d1 d2 sb) =
  ⋆app1 (⇒αβ₊-β{s1} (&&-elim2 be) d2) ⋆trans
  ⋆app2 (⇒αβ₊-β{s2} (&&-elim1 be) d1) ⋆trans
  ⋆base (τ-base sb)
⇒αβ₊-β {s1 · s2} {t1 · t2} be (app d1 d2) =
  ⋆app1 (⇒αβ₊-β{s1} (&&-elim1 be) d1) ⋆trans
  ⋆app2 (⇒αβ₊-β{s2} (&&-elim2 be) d2)
⇒αβ₊-β {ƛ x s} {ƛ x₁ t} be (lam d) = ⋆lam (⇒αβ₊-β{s} be d)

-- parallel reduction preserves the set of bound variables
⇒αβ₊-bvs : preserves-set (⇒αβ₊ tt) bvs _≃_
⇒αβ₊-bvs d = ↝β⋆-bvs (⇒αβ₊-β refl d) 


{- Terms that are path distinct with respect to a set vs including the free variables of t
   parallel reduce to their complete superdevelopments, without alpha steps -}
pathDistinct-sd : ∀{t : Tm}{vs : 𝕃 V} →
           varsub (fvs t) vs ≡ tt → 
           pathDistinct vs t ≡ tt →
           t ⟨ ⇒αβ₊ tt ⟩ (sd t)
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
 - Theorem.

   Any term's α-canonization can be completely superdeveloped, without alpha-steps.

   This version uses superdevelopments instead of developments.
 -
 --------------------------------------------------------------------------------}
⇒αsd : ∀{t : Tm} →
       let a = αcanon t in
        a ⟨ ⇒αβ₊ tt ⟩ sd a 
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
↝β-αsd{t} = ⇒αβ₊-β refl (⇒αsd{t})

