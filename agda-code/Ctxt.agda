open import lib
open import VarInterface

module Ctxt where

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

ctxtDrop : V → Ctxt → Ctxt
ctxtDrop = remove _≃_ 

{-

#-++ : ∀{x : V}{Γ1 Γ2 : Ctxt} →
        x # Γ1 →
        x # Γ2 →
        x # (Γ1 ++ Γ2)
#-++ #empty a2 = a2
#-++ (#skip a1 x) a2 = #skip (#-++ a1 a2) x

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

{-
inCtxtWeaken : ∀ {Γ' Γ : Ctxt}{v x : V} → 
                  inCtxt v (Γ' ++ Γ) →
                  x ≃ v ≡ ff →
                  inCtxt v (Γ' ++ x :: Γ)
inCtxtWeaken {[]} {Γ} i ne = nextInCtxt i (~≃-sym ne)
inCtxtWeaken {y :: Γ'} {Γ} foundInCtxt ne = foundInCtxt
inCtxtWeaken {y :: Γ'} {Γ} (nextInCtxt i x) ne = nextInCtxt (inCtxtWeaken i ne) x
-}

inCtxtExchangeTriv : ∀ {Γ' Γ : Ctxt}{v x : V} → 
                       (i : inCtxt v (Γ' ++ x :: Γ)) →
                       inCtxtExchange i #empty ≡ i 
inCtxtExchangeTriv {z :: Γ'} foundInCtxt = refl
inCtxtExchangeTriv {z :: Γ'} (nextInCtxt i x) rewrite (inCtxtExchangeTriv i) = refl
inCtxtExchangeTriv{[]} i = refl

inCtxtWeaken1 : ∀{Γ1 Γ2 : Ctxt}{x : V} →
                inCtxt x Γ2 →
                x # Γ1 →
                inCtxt x (Γ1 ++ Γ2)
inCtxtWeaken1 {[]} i a = i
inCtxtWeaken1 {x :: Γ1} i (#skip a x₁) = nextInCtxt (inCtxtWeaken1 i a) x₁
             
inCtxtWeaken : ∀{Γ1 Γ Γ2 : Ctxt}{x : V} →
               inCtxt x (Γ1 ++ Γ2) →
               x # Γ →
               inCtxt x (Γ1 ++ Γ ++ Γ2)
inCtxtWeaken {[]} i a = inCtxtWeaken1 i a
inCtxtWeaken {z :: Γ1} foundInCtxt a = foundInCtxt
inCtxtWeaken {z :: Γ1} (nextInCtxt i x) a = nextInCtxt (inCtxtWeaken{Γ1} i a) x

inCtxtWeaken1a : ∀{Γ1 Γ2 : Ctxt}{x y : V} →
                inCtxt y Γ2 →
                y # Γ1 →
                x ≃ y ≡ ff → 
                inCtxt y (Γ1 ++ [ x ] ++ Γ2)
inCtxtWeaken1a i a q = inCtxtWeaken (inCtxtWeaken1 i a) (#skip #empty (~≃-sym q))
{-
inCtxtWeaken1a {[]} i a q = nextInCtxt i (~≃-sym q)
inCtxtWeaken1a {x :: Γ1} i (#skip a x₁) q = nextInCtxt (inCtxtWeaken1a{Γ1} i a q) x₁
-}

strengthenCtxt : ∀{Γ' Γ : Ctxt}{v v' : V} →
                  inCtxt v' (Γ' ++ v :: Γ) →
                  (v ≃ v') ≡ ff →
                  inCtxt v' (Γ' ++ Γ)
strengthenCtxt {[]}{v = v} foundInCtxt ne rewrite ≃-refl{v} with ne
strengthenCtxt {[]} foundInCtxt ne | ()
strengthenCtxt {[]} (nextInCtxt i x) ne = i
strengthenCtxt {z :: Γ'} foundInCtxt ne = foundInCtxt
strengthenCtxt {z :: Γ'} (nextInCtxt i x) ne = nextInCtxt (strengthenCtxt{Γ' = Γ'} i ne) x

weakenStrengthenCtxt : ∀{Γ' Γ : Ctxt}{v v' : V} 
                        {i : inCtxt v' (Γ' ++ v :: Γ)}
                        {e : (v ≃ v') ≡ ff}
                        {a : v' # [ v ]} → 
                        inCtxtWeaken (strengthenCtxt i e) a ≡ i
weakenStrengthenCtxt {[]} {v = v}{i = foundInCtxt}{e} rewrite ≃-refl{v} with e 
weakenStrengthenCtxt {[]} {v = v}{i = foundInCtxt}{e} | ()
weakenStrengthenCtxt {[]} {i = nextInCtxt i x}{a = #skip a b} rewrite ≃-uip b x = refl
weakenStrengthenCtxt {x :: Γ'} {Γ} {v} {.x} {foundInCtxt} {e} {a} = refl
weakenStrengthenCtxt {x :: Γ'} {Γ} {v} {v'} {nextInCtxt i x₁} {e} {a} rewrite weakenStrengthenCtxt{Γ'}{Γ}{v}{v'}{i}{e}{a} = refl

#-deterministic : ∀{v : V}{Γ : Ctxt} →
                   (a : v # Γ) →
                   (a' : v # Γ) →
                   a ≡ a'
#-deterministic #empty #empty = refl
#-deterministic (#skip{v}{y} a x) (#skip a' x') rewrite ≃-uip x x' | #-deterministic a a' = refl





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

-}