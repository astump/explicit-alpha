open import lib
open import VarInterface

module Triangle where

open import Tm 
open import Subst
open import Apart
open import Alpha
open import Renaming
open import Substitution
open import AlphaCanon
open import Takahashi 
open import Parallel

triangle-⇒αβ : ∀{s t t' : Tm}{ρ : Renaming}{b : 𝔹} →
                injectiver ρ ≡ tt → 
                pathDistinct (ranr ρ) t' ≡ tt →
                varsub (fvs s) (domr ρ) ≡ tt → 
                s ⟨ ⇒αβ b ⟩ t →
                Alpha ρ t t' → 
                t' ⟨ ⇒αβ ff ⟩ (αtk s ρ)
triangle-⇒αβ {var v} {var v} {var _} {ρ} {b} _ _ _ var (var u) rewrite u = var
triangle-⇒αβ {var v · s2} {var v · t2} {var v' · t2'} {ρ} j pd vs (app {b1 = b1} {b2} var x₁) (app (var u) rn₁) rewrite u = 
 app{var v'}{t2'}{var v'}{αtk s2 ρ}{ff}{ff} var
   (triangle-⇒αβ {s2} {t2} {t2'} j (&&-elim2 pd) (&&-elim2 vs) x₁ rn₁)

triangle-⇒αβ {sa · sb · s2} {t1 · t2} {t1' · t2'} {ρ} j pd vs (app {b1 = b1} {b2} x x₁) (app rn rn₁) =
 app {t1'} {t2'} {αtk (sa · sb) ρ} {αtk s2 ρ}{ff}{ff}
  (triangle-⇒αβ {sa · sb} {t1} {t1'} {ρ} {b1}
    j {!!} {!!} x rn)
  (triangle-⇒αβ {s2} {t2} {t2'} {ρ} {b2}
    j {!!} {!!} x₁ rn₁)
triangle-⇒αβ {(ƛ y s1) · s2} {(ƛ y t1) · t2} {_ · t2'} {ρ} j pd vs
  (app {b1 = b1} {b2} (lam{s1}{t1}{x}{b1} d1) d2) (app (lam{y}{y'}{t1}{t1'}{ρ} nc ne rn1) rn2) =
  let n = fresh (ranr ρ) in
  let p1 = triangle-⇒αβ{s1}{t1}{t1'}{(y , n) :: ρ}{b1}
             (&&-intro {~ varmem n (ranr ρ)} (~-≡-ff (fresh-distinct{ranr ρ})) j)
             {!!}
             {!!}
             d1
             {!!} in
  let p2 = triangle-⇒αβ{s2}{t2}{t2'}{ρ}{b2}
            {!!} {!!} {!!} d2 rn2 in
  let s1' = αtk s1 ((y , n) :: ρ) in
  let s2' = αtk s2 ρ in
   beta {t2'} {y'} {t1'} {s2'} {s1'} {graft1 s2' n s1'} {ff} {ff}
     p2
     {!!}
     {!!}
triangle-⇒αβ {(ƛ y s1) · s2} {t1 · t2} {t1' · t2'} {ρ} j pd vs (app {b1 = b1} {b2} d1 d2) (app rn1 rn2) =
 {!!}

triangle-⇒αβ {s1 · s2} {t} {t'} {ρ} j pd vs (beta{x = y}{t1' = t1}{t2}{b1 = b1}{b2} d1 d2 sb) rn
 = {!!}

triangle-⇒αβ {ƛ y s} {ƛ z t} {ƛ z' t'} {ρ} {ff} j pd vs (alpha{t' = t''}{b = b} x x₁ x₂ x₃) (lam nc ne rn) =
  let n = fresh (ranr ρ) in
   alpha{z'}{n}{t'}{t''}{αtk s ((y , n) :: ρ)}{b} {!!} {!!} {!!} {!!} 

triangle-⇒αβ {ƛ y s} {ƛ y t} {ƛ y' t'} {ρ} {b} j pd vs (lam d) (lam m ne rn) with keep (y' ≃ fresh (ranr ρ))
triangle-⇒αβ {ƛ y s} {ƛ y t} {ƛ y' t'} {ρ} {b} j pd vs (lam d) (lam m ne rn) | tt , vn rewrite sym (≃-≡{y'} vn) =
  lam{t'}{αtk s ((y , y') :: ρ)}{y'}{ff}
   (triangle-⇒αβ {s} {t} {t'} {(y , y') :: ρ} {b}
     (&&-intro {~ varmem y' (ranr ρ)} (&&-elim1 pd) j)
     (&&-elim2 pd) {!!} d rn)

triangle-⇒αβ {ƛ y s} {ƛ y t} {ƛ y' t'} {ρ} {b} j pd vs (lam d) (lam m ne rn) | ff , vn = 
  let n = fresh (ranr ρ) in
  let r = αtk s ((y , n) :: ρ) in
  let vsr = varsub-remove {fvs s} {domr ρ} {y} vs in
   alpha {y'} {n} {t'} {αtk s ((y , y') :: ρ)} {r}{ff}
     (varmem-varsub-ff {n} {fvs (αtk s ((y , y') :: ρ))}
       {fvs (αc s ((y , y') :: ρ))} (varsub-fvs-tk{αc s ((y , y') :: ρ)})
         (varmem-varsub-ff {n} {fvs (αc s ((y , y') :: ρ))} {y' :: ranr ρ}
           (fvs-αc {s} {(y , y') :: ρ} vsr) h)) vn
     (triangle-⇒αβ {s} {t} {t'} {(y , y') :: ρ}
       (&&-intro {~ varmem y' (ranr ρ)} (~-≡-ff m) j)
       (&&-elim2 pd) vsr d rn) {!!}
 where h : varmem (fresh-ℕ (ranr ρ)) (y' :: ranr ρ) ≡ ff
       h rewrite ~≃-sym{y'} vn = fresh-distinct{ranr ρ}