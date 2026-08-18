{- definition of parallel reduction
-}
open import lib
open import VarInterface

module Parallel where

open import Tm 
open import Subst
open import Apart
open import Renaming
open import AlphaCanon
open import Takahashi 

data ⇒αβ : Tm → Tm → Set where
  var : ∀{v : V} → 
          var v ⟨ ⇒αβ ⟩ var v
  app : ∀{t1 t2 t1' t2' : Tm} →
        t1 ⟨ ⇒αβ ⟩ t1' →
        t2 ⟨ ⇒αβ ⟩ t2' →
        t1 · t2 ⟨ ⇒αβ ⟩ t1' · t2'
  beta : ∀{t1 : Tm}{x : V}{t2 : Tm}{t1' t2' r : Tm} →
         t1 ⟨ ⇒αβ ⟩ t1' →
         t2 ⟨ ⇒αβ ⟩ t2' →        
         Subst t1' x t2' r → 
         (ƛ x t2) · t1 ⟨ ⇒αβ ⟩ r
  alpha : ∀{x x' : V}{t t' r : Tm} →
          x' ∈ t' ≡ ff →                              -- avoid capture
          x ≃ x' ≡ ff → 
          t ⟨ ⇒αβ ⟩ t' →
          Subst (var x') x t' r → 
          (ƛ x t) ⟨ ⇒αβ ⟩ (ƛ x' r)
  lam : ∀{t t' : Tm}{x : V} →
        t ⟨ ⇒αβ ⟩ t' →
        ƛ x t ⟨ ⇒αβ ⟩ ƛ x t'

⇒αβ-refl : ∀{t : Tm} → t ⟨ ⇒αβ ⟩ t
⇒αβ-refl {var x} = var
⇒αβ-refl {t · t₁} = app ⇒αβ-refl ⇒αβ-refl
⇒αβ-refl {ƛ x t} = lam ⇒αβ-refl

varOk-tk : ∀{t : Tm}{vs : 𝕃 V} →
           varsub (fvs t) vs ≡ tt → 
           varOk vs t ≡ tt →
           t ⟨ ⇒αβ ⟩ (tk t)
varOk-tk{var x}{vs} sub ok = var
varOk-tk{var x · t}{vs} sub ok = app var (varOk-tk{t}{vs} (isSublist-++2l{eq = _≃_}{[ x ]}{fvs t}{vs} sub) (&&-elim2 ok))
varOk-tk{t1 · t2 · t3}{vs} sub ok =
 app (varOk-tk{t1 · t2}{vs} (isSublist-++1l{eq = _≃_}{fvs t1 ++ fvs t2}{fvs t3}{vs} sub) (&&-elim1 ok))
     (varOk-tk{t3}{vs} ((isSublist-++2l{eq = _≃_}{fvs t1 ++ fvs t2}{fvs t3}{vs} sub)) (&&-elim2 ok))
varOk-tk{(ƛ x t1) · t2}{vs} sub ok =
  beta {t2} {x} {t1} {tk t2} {tk t1}
    (varOk-tk {t2} {vs} (isSublist-++2l{eq = _≃_}{remove _≃_ x (fvs t1)}{fvs t2}{vs} sub)
       (&&-elim2 ok))
    (varOk-tk {t1} {x :: vs}
      (isSublist-remove{eq = _≃_}{fvs t1}{vs}{x} (λ{x} → ≃-sym{x})
        ((isSublist-++1l{eq = _≃_}{remove _≃_ x (fvs t1)}{fvs t2}{vs} sub)))
      (&&-elim2{~ varmem x vs} (&&-elim1 ok)))
    (substLem (varapart-varsub {bvs (tk t1)} {bvs t1} {fvs (tk t2)} {fvs t2}
                (varsub-bvs{t1}) (varsub-fvs{t2})
                 (varapart-sym {fvs t2} {bvs t1}
                  (varOk-Apart'{t1}{fvs t2}{x :: vs} (&&-elim2{~ varmem x vs} (&&-elim1 ok)) h))))
 where h : varsub (fvs t2) (x :: vs) ≡ tt                  
       h rewrite varsub-++{varrem x (fvs t1)}{fvs t2}{vs} = varsub-trans {fvs t2} {vs} {x :: vs} (&&-elim2 sub) (varsub-++2a{[ x ]}{vs})

varOk-tk{ƛ x t}{vs} sub ok =
 lam (varOk-tk {t} {x :: vs} (isSublist-remove{eq = _≃_}{fvs t}{vs}{x} (λ{x} → ≃-sym{x}) sub) (&&-elim2 ok))


{--------------------------------------------------------------------------------
 - Main theorem 1:

   Any term's α-canonization can be completely developed.
 -
 --------------------------------------------------------------------------------}
⇒αtk : ∀{t : Tm} →
       let a = αcanon t in
        a ⟨ ⇒αβ ⟩ tk a 
⇒αtk{t} = varOk-tk h2 (αc-varOk{t} h)
 where h : varsub (fvs t) (domr (diagonal (fvs t))) ≡ tt
       h rewrite domr-diag{fvs t} = varsub-refl{fvs t}
       hi : varsub (fvs t) (domr (diagonal (fvs t))) ≡ tt
       hi rewrite domr-diag{fvs t} = varsub-refl{fvs t}
       h2 : varsub (fvs (αcanon t)) (ranr (diagonal (fvs t))) ≡ tt
       h2 with fvs-αc{t}{diagonal (fvs t)} hi 
       h2 | u rewrite ranr-diag{fvs t} = u

