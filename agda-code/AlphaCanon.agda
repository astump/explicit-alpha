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
           varOk (domr ρ) t ≡ tt → 
           varOk (ranr ρ) (αc t ρ) ≡ tt
αc-varOk {var x} {ρ} vok = varmem-rename{x}{ρ} vok
αc-varOk {t1 · t2} {ρ} vok = &&-intro (αc-varOk{t1}{ρ} (&&-elim1 vok)) (αc-varOk{t2}{ρ} (&&-elim2 vok))
αc-varOk {ƛ x t} {ρ} vok rewrite fresh-distinct{ranr ρ} = αc-varOk{t}{(x , fresh (ranr ρ)) :: ρ}  (&&-elim2 vok)

varOk-Apart : ∀{t : Tm}{vs : 𝕃 V} →
                varOk vs t ≡ tt →
                varapart vs (bvs t) ≡ tt
varOk-Apart {var x} {vs} ok = varapart-[]{vs}
varOk-Apart {t1 · t2} {vs} ok = varapart-++i{vs}{bvs t1}{bvs t2} (varOk-Apart{t1}{vs} (&&-elim1 ok)) (varOk-Apart{t2}{vs} (&&-elim2 ok))
varOk-Apart {ƛ x t} {vs} ok rewrite refl{x = 0} with varOk-Apart{t}{x :: vs} (&&-elim2 ok) 
varOk-Apart {ƛ x t} {vs} ok | p = 
  list-all-sub {p = λ a → ~ (a ≃ x) && ~ varmem a (bvs t)}
               {λ a → ~ ((a ≃ x) || varmem a (bvs t))} vs
               j
               (list-all-&& {p = λ a → ~ (a ≃ x)} {λ a → ~ varmem a (bvs t)} vs
                 (list-all-sub {p = λ a → ~ x ≃ a}{λ a → ~ a ≃ x} vs h
                   (list-member-list-all-ff2{eq = _≃_}{x}{vs} (~-≡-tt (&&-elim1 ok))))
                 (&&-elim2 p))
   where h : ∀(a : ℕ) → ~ x ≃ a ≡ tt → ~ a ≃ x ≡ tt
         h a u rewrite ~≃-sym{x} (~-≡-tt{x ≃ a} u) = refl
         j : ∀(a : ℕ) →
             ~ a =ℕ x && ~ varmem a (bvs t) ≡ tt →
             ~ (a =ℕ x || varmem a (bvs t)) ≡ tt
         j a v rewrite ~-≡-tt{a ≃ x} (&&-elim1 v) = &&-elim2 v