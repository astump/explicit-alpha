{-# OPTIONS --allow-unsolved-metas #-}
open import lib hiding (_>>=_ ; return ; _∘_)
open import VarInterface

module AlphaMInternal where

--open import Tm 
open import Renaming
open import Monad

------ ###

αMM : Tm → Set
αMM t = (ρ : Renaming)(vs : 𝕃 V) →
           varsub (fvs t) (domr ρ) ≡ tt →
           varsub (ranr ρ) vs ≡ tt →
         Σ Tm (λ t' → Σ (𝕃 V) (λ vs' →
           varsub (fvs t') (ranr ρ) ≡ tt ∧
           varapart vs vs' ≡ tt ∧
           varsub (bvs t') vs' ≡ tt ∧ 
           varunique (bvs t')
         ))

data αM(X : Set) : Set where
 αm : αMM X → αM X

runαm : ∀{X : Set} → αM X → αMM X
runαm (αm h) = h

withFresh : ∀{X : Set} → V → (V → αM X) → αM X
withFresh{X} v c = αm h'
 where h' : αMM X
       h' ρ vs =
         let n = fresh vs in
           runαm (c n) ((v , n) :: ρ) (n :: vs)

renamev : V → αM V
renamev v = αm h
 where h : αMM V
       h ρ vs = rename ρ v , vs


returnα : ∀{X : Set} → X → αM X
returnα v = αm (λ ρ vs → (v , vs))

_>>=α_ : ∀{A B : Set} → αM A → (A → αM B) → αM B
_>>=α_{A}{B} m g = αm (λ ρ vs → 
                        let p = (runαm m) ρ vs in
                          runαm (g (fst p)) ρ (snd p))

infix 9 _>>=α_

instance
 αM-Monad : Monad αM  
 αM-Monad = record { return = returnα ; _>>=_ = _>>=α_ }

evalαm : ∀{X : Set} → αM X → Renaming → 𝕃 V → X
evalαm m ρ vs = fst (runαm m ρ vs)

Pre : Set₁
Pre = Renaming → 𝕃 V → Set
Post : Set → Set₁
Post X = Renaming → 𝕃 V → (X × 𝕃 V) → Set

αM-hoare : ∀{X : Set} →
           (pre : Pre) →
           (post : Post X) →
           αM X → 
           Set
αM-hoare{X} pre post m = ∀{ρ : Renaming}{vs : 𝕃 V} →
                         pre ρ vs →
                         post ρ vs (runαm m ρ vs)

returnα-hoare : ∀{X : Set}{x : X} →
                αM-hoare{X} (λ _ _ → ⊤) (λ ρ vs p → vs ≡ snd p ∧ x ≡ fst p) (returnα x)
returnα-hoare _ = refl , refl

bindα-hoare : ∀{X Y : Set}{m1 : αM X}{m2 : X → αM Y}
               {pre1 : Pre}
               {post1 : Post X}               
               {pre2 : X → Pre}
               {post2 : X → Post Y} →
               αM-hoare{X} pre1 post1 m1 →
               (∀{x : X} → αM-hoare{Y} (pre2 x) (post2 x) (m2 x)) →                
               αM-hoare{Y}
                 (λ ρ vs →
                     pre1 ρ vs ∧
                     (∀{x : X}{vs' : 𝕃 V} → post1 ρ vs (x , vs') → pre2 x ρ vs'))
                 (λ ρ vs p →
                   ∃ (X × 𝕃 V) (λ p' →  -- p' is the intermediate result obtained from m1
                   post1 ρ vs p' ∧ -- the intermediate state satisfies the postcondition for m1
                   post2 (fst p')
                     ρ (snd p') -- the starting state for m2
                     (runαm (m2 (fst p')) ρ (snd p')))) -- the ending state for m2, beginning from the intermediate state
                 (m1 >>=α m2)
bindα-hoare{X}{Y}{m1}{m2}{pre1}{post1}{pre2}{post2} d1 d2 {ρ}{vs} (u1 , u2) =
  (runαm m1 ρ vs) , d1 u1 , d2{fst (runαm m1 ρ vs)}{ρ}{snd (runαm m1 ρ vs)}
    (u2 (cong-pred (λ q → post1 ρ vs q) (sym (surj-×{p = runαm m1 ρ vs})) (d1 u1)))

{-
αM-consequence : ∀{X : Set}
                 {pre1 pre1' : Pre}
                 {post1 post1' : Post X}               
                 {m : αM X} →
                 αM-hoare pre1 post1 m →
                 (∀{ρ}{vs} → pre1' ρ vs → pre1 ρ vs) →
                 (∀{ρ}{vs}{x} → post1 ρ vs x → post1' ρ vs x) →
                 αM-hoare pre1' post1' m
αM-consequence = {!!}
-}

