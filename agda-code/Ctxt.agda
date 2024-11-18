open import lib
open import VarInterface

module Ctxt(vi : VI) where

open VI vi

Ctxt : Set
Ctxt = 𝕃 V

data inCtxt (x : V) : Ctxt → Set where
  foundInCtxt : ∀{Γ : Ctxt} →
                inCtxt x (x :: Γ)
  nextInCtxt :  ∀{x' : V}{Γ : Ctxt} →
                inCtxt x Γ →
                x ≃ x' ≡ ff → 
                inCtxt x (x' :: Γ)

data _#_ : V → Ctxt → Set where
  #empty : ∀{x : V} → x # []
  #skip : ∀{x y : V}{Γ : Ctxt} →
          x # Γ →
          x ≃ y ≡ ff →
          x # (y :: Γ)


inCtxtExchange : ∀ {Γ'' Γ' Γ : Ctxt}{v x : V} → 
                  inCtxt v (Γ'' ++ Γ' ++ x :: Γ) →
                  x # Γ' →
                  inCtxt v (Γ'' ++ x :: Γ' ++ Γ)
inCtxtExchange {[]} {[]} {Γ} i a = i
inCtxtExchange {[]} {y :: Γ'} {Γ} foundInCtxt (#skip a x) = nextInCtxt foundInCtxt (~≃-sym x)
inCtxtExchange {[]} {y :: Γ'} {Γ} (nextInCtxt i x) (#skip a x₁) with inCtxtExchange{[]}{Γ'}{Γ} i a 
inCtxtExchange {[]} {y :: Γ'} {Γ} (nextInCtxt i x) (#skip a x₁) | foundInCtxt = foundInCtxt
inCtxtExchange {[]} {y :: Γ'} {Γ} (nextInCtxt i x) (#skip a x₁) | nextInCtxt u x₂ = nextInCtxt (nextInCtxt u x) x₂
inCtxtExchange {y :: Γ''} {Γ'} {Γ} foundInCtxt a = foundInCtxt
inCtxtExchange {y :: Γ''} {Γ'} {Γ} (nextInCtxt i x) a = nextInCtxt (inCtxtExchange i a) x


inCtxtWeaken : ∀ {Γ' Γ : Ctxt}{v x : V} → 
                  inCtxt v (Γ' ++ Γ) →
                  x ≃ v ≡ ff →
                  inCtxt v (Γ' ++ x :: Γ)
inCtxtWeaken {[]} {Γ} i ne = nextInCtxt i (~≃-sym ne)
inCtxtWeaken {y :: Γ'} {Γ} foundInCtxt ne = foundInCtxt
inCtxtWeaken {y :: Γ'} {Γ} (nextInCtxt i x) ne = nextInCtxt (inCtxtWeaken i ne) x

inCtxtExchangeTriv : ∀ {Γ' Γ : Ctxt}{v x : V} → 
                       (i : inCtxt v (Γ' ++ x :: Γ)) →
                       inCtxtExchange i #empty ≡ i 
inCtxtExchangeTriv {z :: Γ'} foundInCtxt = refl
inCtxtExchangeTriv {z :: Γ'} (nextInCtxt i x) rewrite (inCtxtExchangeTriv i) = refl
inCtxtExchangeTriv{[]} i = refl

inCtxt++ : ∀{Γ' Γ : Ctxt}{x : V} →
             inCtxt x Γ →
             x # Γ' →
             inCtxt x (Γ' ++ Γ)
inCtxt++ {[]} i a = i
inCtxt++ {z :: Γ'} i (#skip a x) = nextInCtxt (inCtxt++ i a) x

strengthenCtxt : ∀{Γ' Γ : Ctxt}{v v' : V} →
                  inCtxt v' (Γ' ++ v :: Γ) →
                  (v ≃ v') ≡ ff →
                  inCtxt v' (Γ' ++ Γ)
strengthenCtxt {[]}{v = v} foundInCtxt ne rewrite ≃-refl{v} with ne
strengthenCtxt {[]} foundInCtxt ne | ()
strengthenCtxt {[]} (nextInCtxt i x) ne = i
strengthenCtxt {z :: Γ'} foundInCtxt ne = foundInCtxt
strengthenCtxt {z :: Γ'} (nextInCtxt i x) ne = nextInCtxt (strengthenCtxt{Γ' = Γ'} i ne) x


{-

{-





{-
inCtxt# : ∀{Γ : Ctxt}{x x' : V}{T : Tp} →
            inCtxt x T Γ →
            x' # Γ →
            x ≃ x' ≡ ff
inCtxt# foundInCtxt (#skip a x) = ~≃-sym x
inCtxt# (nextInCtxt i x) (#skip a x₁) = inCtxt# i a
-}
-}-}