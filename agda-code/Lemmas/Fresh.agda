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
open import Fresh

Varlt-neq : ∀{x n : V} →
            Varlt x n →
            n ≃ x ≡ ff
Varlt-neq{x}{n} ((y , refl) , v) with keep ((y ++ x) ≃ x)
Varlt-neq{x}{n} ((y , refl) , v) | tt , eq = ⊥-elim (v (sym (≃-≡{y ++ x} eq)))
Varlt-neq{x}{n} ((y , refl) , v) | ff , eq = eq

bounded-not-varmem : ∀{n : V}{vs : 𝕃 V} →
                     Ubounded vs n → 
                     varmem n vs ≡ ff
bounded-not-varmem {n} {[]} bd = refl
bounded-not-varmem {n} {x :: vs} (bd1 , bd2) rewrite Varlt-neq{x}{n} bd1 = bounded-not-varmem{n}{vs} bd2

Ubounded-++ : ∀{l1 l2 : 𝕃 V}{n : V} →
             Ubounded (l1 ++ l2) n →
             Ubounded l1 n ∧ Ubounded l2 n 
Ubounded-++{l1}{l2}{n} bd = all-pred-append2 {V} {Vargt n} bd

Varle-:: : ∀{x n : V}{b : 𝔹} →
           Varle x n →
           Varle x (b :: n)
Varle-::{x}{n}{b} (y , refl) = Suffix-:: {𝔹} {b} {x} {n} (y , refl) 

Vargt-:: : ∀{n x : V}{b : 𝔹} →
           Vargt n x →
           Vargt (b :: n) x
Vargt-::{n}{x}{b} ((y , refl) , u2) = Varle-:: {x} {n} (y , refl) , invert++

Vargt-::2 : ∀{n : V}{b : 𝔹} →
            Vargt (b :: n) n
Vargt-::2{n}{b} = ([ b ] , refl) , (invert++{𝔹}{b}{n}{[]})

Ubounded-:: : ∀{vs : 𝕃 V}{n : V}{b : 𝔹} →
             Ubounded vs n →
             Ubounded vs (b :: n) 
Ubounded-::{vs}{n}{b} u = all-pred-sub {P = Vargt n} {Q = Vargt (b :: n)} vs (λ a → Vargt-::{n}{a}{b}) u

Varle-cong : ∀{n b c : V} → Varle n c → b ≃ c ≡ tt → Varle n b
Varle-cong{nn}{b}{c} v u rewrite ≃-≡{b} u = v