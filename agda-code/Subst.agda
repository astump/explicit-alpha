open import lib
open import VarInterface

module Subst(vi : VI) where

open VI vi
open import Tm vi
open import Ctxt vi
open import Weaken vi


data Subst : ∀{Γ' Γ : Ctxt} → Tm Γ → (v : V) → Tm (Γ' ++ v :: Γ) → Tm (Γ' ++ Γ) → Set where
  substVarFound : ∀{Γ' Γ : Ctxt}{t : Tm Γ}{t' : Tm (Γ' ++ Γ)}{v : V}
                  (a : v # Γ') →
                  Weaken{[]} t t' → 
                  Subst t v (var v (inCtxtWeaken1 foundInCtxt a)) t'
  substVarNot : ∀{Γ' Γ : Ctxt}{t : Tm Γ}{v v' : V}
                  (a : v ≃ v' ≡ ff)
                  (i : inCtxt v' (Γ' ++ v :: Γ)) → 
                  Subst t v (var v' i) (var v' (strengthenCtxt i a))
  substApp : ∀{Γ' Γ : Ctxt}{t : Tm Γ}{v : V}
              {t1 t2 : Tm (Γ' ++ v :: Γ)}
              {t1' t2' : Tm (Γ' ++ Γ) } → 
              Subst t v t1 t1' →
              Subst t v t2 t2' →
              Subst t v (t1 · t2) (t1' · t2')
  substLam : ∀{Γ' Γ : Ctxt}{t : Tm Γ}{v x : V}
              {t1 : Tm (x :: Γ' ++ v :: Γ)}
              {t1' : Tm (x :: Γ' ++ Γ)} → 
              Subst t v t1 t1' →
              Subst t v (ƛ x t1) (ƛ x t1')

substDeterministic : ∀{Γ' Γ : Ctxt}
                      {t1 : Tm Γ}
                      {v : V}
                      {t2 : Tm (Γ' ++ v :: Γ)}
                      {r1 r2 : Tm (Γ' ++ Γ)} →
                      Subst t1 v t2 r1 →
                      Subst t1 v t2 r2 →
                      r1 ≡ r2
substDeterministic{Γ'}{Γ}{v = v} (substVarFound a x) s2 with (inCtxtWeaken1{Γ'}{v :: Γ} foundInCtxt a)
substDeterministic {_} {_} {v = _} (substVarFound a x) (substVarFound a₁ x₁) | .(inCtxtWeaken1 foundInCtxt a₁) = weakenDeterministic x x₁
substDeterministic {_} {_} {v = v} (substVarFound a x) (substVarNot a₁ .i) | i with trans (sym a₁) (≃-refl {v})
substDeterministic {_} {_} {v = v} (substVarFound a x) (substVarNot a₁ .i) | i | ()
substDeterministic {v = v} (substVarNot a .(inCtxtWeaken1 foundInCtxt a₁)) (substVarFound a₁ x) with trans (sym a) (≃-refl {v})
substDeterministic {v = v} (substVarNot a .(inCtxtWeaken1 foundInCtxt a₁)) (substVarFound a₁ x) | ()
substDeterministic {v = v} (substVarNot a i) (substVarNot a₁ .i) rewrite ≃-uip a a₁ = refl
substDeterministic (substApp s1 s2) (substApp s1' s2') rewrite substDeterministic s1 s1' | substDeterministic s2 s2' = refl
substDeterministic (substLam s) (substLam s') rewrite substDeterministic s s' = refl


weakenSubst : ∀{Γ' Γ : Ctxt}{x y : V}{i : inCtxt y Γ}{t : Tm (Γ' ++ x :: Γ)}{r : Tm (Γ' ++ Γ)} →
               Subst (var y i) x t r →
               x ≃ y ≡ ff → 
               Σ[ w ∈ Tm (Γ' ++ x :: Γ) ] Weaken{Γ'}{[ x ]}{Γ} r w
weakenSubst{Γ'}{Γ}{x}{y} (substVarFound a (weakenVar i a')) q =
  var y (inCtxtWeaken1a i a' q) ,
  weakenVar{Γ'}{[ x ]}{Γ}{y}
    (inCtxtWeaken1 i a')
    (#skip #empty (~≃-sym q)) 
weakenSubst{Γ'}{Γ}{v} (substVarNot{v' = v'} a i) q = var v' i , h
  where u : var v' i ≡ var v' (inCtxtWeaken (strengthenCtxt i a) ((#skip #empty (~≃-sym a))))
        u  = cong (λ i → var v' i) (sym (weakenStrengthenCtxt{Γ'}{Γ}{v}{v'}{i}{a}{(#skip #empty (~≃-sym a))}))
        h : Weaken (var v' (strengthenCtxt i a)) (var v' i)
        h = cong-pred (Weaken (var v' (strengthenCtxt i a)))
              (sym u) (weakenVar (strengthenCtxt i a) (#skip #empty (~≃-sym a)))
weakenSubst (substApp s1 s2) q with weakenSubst s1 q | weakenSubst s2 q
weakenSubst (substApp s1 s2) q | w1 , r1 | w2 , r2 = w1 · w2 , weakenApp r1 r2
weakenSubst (substLam s) q with weakenSubst s q
weakenSubst (substLam{x = x} s) q | w , r = ƛ x w , weakenLam r

swapVarsLemma : ∀{Γ' Γ : Ctxt}{x y : V}{t : Tm (Γ' ++ x :: Γ)}{t' : Tm (Γ' ++ x :: y :: Γ)}{r : Tm (Γ' ++ y :: Γ)} →
               (neq : x ≃ y ≡ ff) → 
               Weaken{Γ' ++ [ x ]}{[ y ]}
                 (cong-pred Tm (sym (++-assoc Γ' [ x ] Γ)) t)
                 (cong-pred Tm (sym (++-assoc Γ' [ x ] (y :: Γ))) t') → 
               Subst{Γ'}{y :: Γ} (var y foundInCtxt) x t' r →
               Σ[ w ∈ Tm (Γ' ++ y :: x :: Γ) ]
                 Weaken{Γ' ++ [ y ]}{[ x ]}{Γ}
                   (cong-pred Tm (sym (++-assoc Γ' [ y ] Γ)) r)
                   (cong-pred Tm (sym (++-assoc Γ' [ y ] (x :: Γ))) w)  ∧
                 Subst (var x foundInCtxt) y w t
swapVarsLemma {Γ'} {Γ} {x} {y} {var z i} {t'} {r} neq w s = {!!}
swapVarsLemma {Γ'} {Γ} {x} {y} {t1 · t2} {t'} {r} neq w s = {!!}
swapVarsLemma {Γ'} {Γ} {x} {y} {ƛ z t} {t'} {r} neq w s = {!!}
