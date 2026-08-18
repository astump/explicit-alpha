{- The function proposed by Takahashi to compute the maximum
   parallel reduct of t.
-}
open import lib hiding (_>>=_ ; return ; _∘_)
open import relations
open import diamond
open import VarInterface
open import Monad

module AlphaCanon where

open import Tm 
open import Renaming

αc : Tm → Renaming → Tm
αc (var x) ρ = var (rename ρ x)
αc (t1 · t2) ρ = αc t1 ρ · αc t2 ρ
αc (ƛ x t) ρ =
  let n = fresh (ranr ρ) in
    ƛ n (αc t ((x , n) :: ρ))

αcanon : Tm → Tm
αcanon t = αc t (diagonal (fvs t))

{- varOk vs t

   This means that the variables in vs are not bound in t
   and hereditarily for subterms of t where we add the bound
   variables above those subterms, to vs.

   So if x is bound somewhere in t, then it cannot be bound again
   below that point.
-}
varOk : 𝕃 V → Tm → 𝔹
varOk vs (var x) = varmem x vs
varOk vs (t1 · t2) = varOk vs t1 && varOk vs t2
varOk vs (ƛ x t) = ~ varmem x vs && varOk (x :: vs) t



αc-varOk : ∀{t : Tm}{ρ : Renaming} →
             varsub (fvs t) (domr ρ) ≡ tt → 
             varOk (ranr ρ) (αc t ρ) ≡ tt
αc-varOk {var x}{ρ} sb = varmem-rename{x}{ρ} (&&-elim1 sb)
αc-varOk {t1 · t2}{ρ} sb rewrite varsub-++{fvs t1}{fvs t2}{domr ρ} | αc-varOk{t1}{ρ} (&&-elim1 sb) 
                               | αc-varOk{t2}{ρ} (&&-elim2 sb) = refl
αc-varOk {ƛ x t}{ρ} sb =
  &&-intro {~ varmem (fresh (ranr ρ)) (ranr ρ)} (~-≡-ff (fresh-distinct{ranr ρ})) 
   (αc-varOk {t} {(x , fresh (ranr ρ)) :: ρ} (varsub-remove {fvs t} {domr ρ} {x} sb))


varOk-Apart' : ∀{t : Tm}{vs vs' : 𝕃 V} →
                varOk vs' t ≡ tt →
                varsub vs vs' ≡ tt → 
                varapart vs (bvs t) ≡ tt
varOk-Apart' {var x} {vs} {vs'} ok sb = varapart-[]{vs}
varOk-Apart' {t1 · t2} {vs} {vs'} ok sb = varapart-++i {vs} {bvs t1} {bvs t2}
                                            (varOk-Apart'{t1}{vs}{vs'} (&&-elim1 ok) sb) 
                                            (varOk-Apart'{t2}{vs}{vs'} (&&-elim2 ok) sb) 
varOk-Apart' {ƛ x t} {vs} {vs'} ok sb = 
 varapart-++i {vs} {[ x ]} {bvs t}
   (varapart-sym {[ x ]} {vs} h )
   (varOk-Apart' {t} {vs} {x :: vs'} (&&-elim2 ok) (varsub-++2{[ x ]}{vs}{vs'} sb))
 where h : varapart [ x ] vs ≡ tt
       h rewrite varmem-sub-ff{x}{vs}{vs'} sb (~-≡-tt {varmem x vs'} (&&-elim1 ok)) = refl

fvs-αc : ∀{t : Tm}{ρ : Renaming} →
         varsub (fvs t) (domr ρ) ≡ tt → 
         varsub (fvs (αc t ρ)) (ranr ρ) ≡ tt
fvs-αc {var x} {ρ} sb rewrite varmem-rename{x}{ρ} (&&-elim1 sb) = refl
fvs-αc {t1 · t2} {ρ} sb rewrite varsub-++{fvs t1}{fvs t2}{domr ρ} =
 varsub-++il {fvs (αc t1 ρ)} {fvs (αc t2 ρ)} {ranr ρ}
    (fvs-αc{t1}{ρ} (&&-elim1 sb)) (fvs-αc{t2}{ρ} (&&-elim2 sb))
fvs-αc {ƛ x t} {ρ} sb = varsub-remove1 {fvs (αc t ((x , fresh (ranr ρ)) :: ρ))} {ranr ρ}
                         {fresh (ranr ρ)} (fvs-αc {t} {(x , fresh (ranr ρ)) :: ρ} (varsub-remove {fvs t} {domr ρ} {x} sb))

