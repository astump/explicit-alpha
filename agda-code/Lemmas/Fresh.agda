{-# OPTIONS --allow-unsolved-metas #-}

open import lib hiding (_>>=_ ; return ; _∘_)
open import VarInterface
open import VarImpls

module Lemmas.Fresh where

open VI VI-𝕃𝔹

open import Tm VI-𝕃𝔹
open import VarOps VI-𝕃𝔹
open import Renaming VI-𝕃𝔹
open import Lemmas.Renaming VI-𝕃𝔹
open import Lemmas.VarInterface VI-𝕃𝔹
open import Lemmas.VarOps VI-𝕃𝔹
open import Fresh

Varlt-neq : ∀{x n : V} →
            Varlt x n →
            n ≃ x ≡ ff
Varlt-neq{x}{n} ((y , refl) , v) with keep ((y ++ x) ≃ x)
Varlt-neq{x}{n} ((y , refl) , v) | tt , eq = ⊥-elim (v (sym (≃-≡{y ++ x} eq)))
Varlt-neq{x}{n} ((y , refl) , v) | ff , eq = eq

Varle-refl : ∀{n : V} → Varle n n
Varle-refl {n} = [] , refl

bounded-not-varmem : ∀{n : V}{vs : 𝕃 V} →
                     Ubounded vs n → 
                     varmem n vs ≡ ff
bounded-not-varmem {n} {vs} bd = bd Varle-refl

Ubounded-++ : ∀{l1 l2 : 𝕃 V}{n : V} →
              Ubounded (l1 ++ l2) n →
              Ubounded l1 n ∧ Ubounded l2 n 
Ubounded-++{l1}{l2}{n} bd = h1 , h2
 where h1 : Ubounded l1 n
       h1{v} u with bd{v} u 
       h1{v} u | r rewrite varmem-++ v l1 l2 = fst (||-ff-elim{varmem v l1} r)
       h2 : Ubounded l2 n
       h2{v} u with bd{v} u 
       h2{v} u | r rewrite varmem-++ v l1 l2 = snd (||-ff-elim{varmem v l1} r)


Varle-:: : ∀{x n : V}{b : 𝔹} →
           Varle x n →
           Varle x (b :: n)
Varle-::{x}{n}{b} (y , refl) = Suffix-:: {𝔹} {b} {x} {n} (y , refl) 

Varle-::1 : ∀{x n : V}{b : 𝔹} →
            Varle (b :: n) x → 
            Varle n x 
Varle-::1{x}{n}{b} (y , u) rewrite sym u = y ++ [ b ] , ++-assoc y [ b ] n

Vargt-:: : ∀{n x : V}{b : 𝔹} →
           Vargt n x →
           Vargt (b :: n) x
Vargt-::{n}{x}{b} ((y , refl) , u2) = Varle-:: {x} {n} (y , refl) , invert++

Vargt-::2 : ∀{n : V}{b : 𝔹} →
            Vargt (b :: n) n
Vargt-::2{n}{b} = ([ b ] , refl) , (invert++{𝔹}{b}{n}{[]})

Varle-cong : ∀{n b c : V} → Varle n c → b ≃ c ≡ tt → Varle n b
Varle-cong{nn}{b}{c} v u rewrite ≃-≡{b} u = v

Ubounded-:: : ∀{vs : 𝕃 V}{n : V}{b : 𝔹} →
             Ubounded vs n →
             Ubounded vs (b :: n) 
Ubounded-::{vs}{n}{b} u {v} le = u (Varle-::1 le)

varmem-fresh : ∀{vs : 𝕃 V}{x : V} →
               varmem x vs ≡ tt →
               length x < length (fresh vs) ≡ tt 
varmem-fresh {v :: vs} {x} m with ||-elim {x ≃ v} m
varmem-fresh {v :: vs} {x} m | inj₁ i rewrite ≃-≡{x} i with keep (v longer (foldr longer-list [] vs)) 
varmem-fresh {v :: vs} {x} m | inj₁ i | tt , eq rewrite eq = <-suc (length v)
varmem-fresh {v :: vs} {x} m | inj₁ i | ff , eq rewrite eq with length-longer-ff{𝔹}{v}{foldr longer-list [] vs} eq 
varmem-fresh {v :: vs} {x} m | inj₁ i | ff , eq | q =
 ≤<suc{length v}{length (foldr longer-list [] vs)}
  (<ff{length (foldr longer-list [] vs)}{length v} q)
varmem-fresh {v :: vs} {x} m | inj₂ i with keep (v longer (foldr longer-list [] vs))
varmem-fresh {v :: vs} {x} m | inj₂ i | tt , eq rewrite eq =
  <-trans {length x} {suc (length (foldr longer-list [] vs))}
          {suc (length v)}
      (varmem-fresh {vs} {x} i)
      (length-longer {𝔹} {v} {foldr longer-list [] vs} eq)
varmem-fresh {v :: vs} {x} m | inj₂ i | ff , eq rewrite eq = (varmem-fresh {vs} {x} i)

length-longer-varmem : ∀{v : V}{vs : 𝕃 V} →
                        length (foldr longer-list [] vs) < length v ≡ tt →
                        varmem v vs ≡ ff
length-longer-varmem {v} {[]} u = refl
length-longer-varmem {v} {x :: vs} u with keep (x longer (foldr longer-list [] vs))
length-longer-varmem {v} {x :: vs} u | tt , p rewrite p with keep (v ≃ x)
length-longer-varmem {v} {x :: vs} u | tt , p | tt , q rewrite ≃-≡{v} q rewrite <-irrefl (length x) with u
length-longer-varmem {v} {x :: vs} u | tt , p | tt , q | ()
length-longer-varmem {v} {x :: vs} u | tt , p | ff , q rewrite q =
 length-longer-varmem {v} {vs}
   (<-trans{length (foldr longer-list [] vs)}{length x}{length v}
     (length-longer{𝔹}{x}{foldr longer-list [] vs} p) u)
length-longer-varmem {v} {x :: vs} u | ff , p rewrite p rewrite length-longer-varmem{v}{vs} u with keep (v ≃ x)
length-longer-varmem {v} {x :: vs} u | ff , p | tt , q rewrite q rewrite ≃-≡{v} q
 with length-longer-ff{𝔹}{x}{foldr longer-list [] vs} p
length-longer-varmem {v} {x :: vs} u | ff , p | tt , q | zz rewrite u with zz
length-longer-varmem {v} {x :: vs} u | ff , p | tt , q | zz | ()
length-longer-varmem {v} {x :: vs} u | ff , p | ff , q rewrite q = refl

Ubounded-fresh : ∀{vs : 𝕃 V} → Ubounded vs (fresh vs)
Ubounded-fresh {[]} _ = refl
Ubounded-fresh {x :: vs} {v} le with Suffix-length{𝔹}{fresh (x :: vs)}{v} le 
Ubounded-fresh {x :: vs} {v} le | p with keep (x longer (foldr longer-list [] vs))
Ubounded-fresh {x :: vs} {v} le | p | tt , eq rewrite eq with keep (v ≃ x)
Ubounded-fresh {x :: vs} {v} le | p | tt , eq | tt , eq' rewrite ≃-≡{v} eq' = ⊥-elim (Suffix-::-ff{𝔹}{ff}{x} le)
Ubounded-fresh {x :: vs} {v} (y , q) | p | tt , eq | ff , eq' rewrite eq'
 with length-longer{𝔹}{x}{foldr longer-list [] vs} eq
Ubounded-fresh {x :: vs} {v} (y , q) | p | tt , eq | ff , eq' | uu
 with <≤-trans{length (foldr longer-list [] vs)}{length x}{length v} uu
          (<≤{length x} (<≤-trans{length x}{suc (length x)}{length v} (<-suc (length x)) p)) 
Ubounded-fresh {x :: vs} {v} (y , q) | p | tt , eq | ff , eq' | uu | qq = length-longer-varmem {v} {vs} qq
Ubounded-fresh {x :: vs} {v} le | p | ff , eq rewrite eq
 with <ff{length (foldr longer-list [] vs)} (length-longer-ff{𝔹}{x}{foldr longer-list [] vs} eq )
Ubounded-fresh {x :: vs} {v} le | p | ff , eq | q with keep (v ≃ x) 
Ubounded-fresh {x :: vs} {v} le | p | ff , eq | q | tt , uu rewrite ≃-≡{v} uu
 with ≤-suc2 (length (foldr longer-list [] vs))
Ubounded-fresh {x :: vs} {v} le | p | ff , eq | q | tt , uu | pp
 with ≤-trans{suc (length (foldr longer-list [] vs))}{length x}{length (foldr longer-list [] vs)} p q 
Ubounded-fresh {x :: vs} {v} le | p | ff , eq | q | tt , uu | pp | qq rewrite pp with qq
Ubounded-fresh {x :: vs} {v} le | p | ff , eq | q | tt , uu | pp | qq | ()
Ubounded-fresh {x :: vs} {v} le | p | ff , eq | q | ff , uu rewrite uu = Ubounded-fresh {vs} {v} le
