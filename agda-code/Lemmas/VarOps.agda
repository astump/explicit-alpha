open import lib
open import bool-relations
open import functions
open import VarInterface

module Lemmas.VarOps(vi : VI) where

open VI vi 

open import Lemmas.VarInterface vi
open import VarOps vi

varsub-++il : ∀{l1 l2 l3 : 𝕃 V} →
                varsub l1 l3 ≡ tt →
                varsub l2 l3 ≡ tt →
                varsub (l1 ++ l2) l3 ≡ tt
varsub-++il{l1}{l2}{l3} = isSublist-++il{eq = _≃_}{l1}{l2}{l3} 

varsub-++-cong : ∀{l1 l2 l3 : 𝕃 V} →
                  varsub l2 l3 ≡ tt → 
                  varsub (l1 ++ l2) (l1 ++ l3) ≡ tt
varsub-++-cong{l1}{l2}{l3} = isSublist-++-cong{V}{_≃_}{l1}{l2}{l3} (λ{x} → ≃-refl{x})

varsub-trans : ∀{l1 l2 l3 : 𝕃 V} →
                varsub l1 l2 ≡ tt →
                varsub l2 l3 ≡ tt →
                varsub l1 l3 ≡ tt
varsub-trans{l1}{l2}{l3} = isSublist-trans{eq = _≃_}{l1}{l2}{l3} ≃-≡

varsub-++-merge : ∀ {l1 l1' l2 l2' : 𝕃 V} →
                    varsub l1 l1' ≡ tt →
                    varsub l2 l2' ≡ tt →                       
                    varsub (l1 ++ l2) (l1' ++ l2') ≡ tt
varsub-++-merge{l1}{l1'}{l2}{l2'} = isSublist-++-merge{eq = _≃_}{l1}{l1'}{l2}{l2'} ≃-≡ (λ{x} → ≃-refl{x})

varsub-++1 : ∀ {l1 l2 : 𝕃 V} →
             varsub l1 (l1 ++ l2) ≡ tt
varsub-++1{l1}{l2} = isSublist-++1{eq = _≃_} {l1}{l2} (λ{x} → ≃-refl{x})

varsub-++1l : ∀{l1 l2 l3 : 𝕃 V} →
              varsub (l1 ++ l2) l3 ≡ tt →
              varsub l1 l3 ≡ tt
varsub-++1l{l1}{l2}{l3} = isSublist-++1l{V}{_≃_}{l1}{l2}{l3}              

varsub-++2l : ∀{l1 l2 l3 : 𝕃 V} →
              varsub (l1 ++ l2) l3 ≡ tt →
              varsub l2 l3 ≡ tt
varsub-++2l{l1}{l2}{l3} = isSublist-++2l{V}{_≃_}{l1}{l2}{l3}              

varsub-++2a : ∀ {l1 l2 : 𝕃 V} →
             varsub l2 (l1 ++ l2) ≡ tt
varsub-++2a{l1}{l2} = isSublist-++2a{eq = _≃_} {l1}{l2} (λ{x} → ≃-refl{x})

varsub-++2 : ∀{l1 l2 l2' : 𝕃 V} →
             varsub l2 l2' ≡ tt →
             varsub l2 (l1 ++ l2') ≡ tt
varsub-++2{l1}{l2}{l2'} = isSublist-++2{V}{_≃_}{l1}{l2}{l2'} (λ{x} → ≃-refl{x})

varsubs-++2 : ∀{n : ℕ}{l1 : 𝕃 V}{l2 : 𝕍 (𝕃 V) n}{l2' : 𝕃 V} →
             varsubs l2 (repeat𝕍 l2' n) ≡ tt → 
             varsubs l2 (repeat𝕍 (l1 ++ l2') n) ≡ tt
varsubs-++2 {zero} {l1} {[]} {l2'} u = refl
varsubs-++2 {suc n} {l1} {vs :: l2} {l2'} u =
 &&-intro {varsub vs (l1 ++ l2')}
   (varsub-++2{l1}{vs}{l2'} (&&-elim1 u))
   (varsubs-++2{n}{l1}{l2}{l2'} (&&-elim2 u))

varsub-++3 : ∀{l1 l1' l2 : 𝕃 V} →
             varsub l1 l1' ≡ tt →
             varsub l1 (l1' ++ l2) ≡ tt
varsub-++3{l1}{l1'}{l2} = isSublist-++3{V}{_≃_}{l1}{l1'}{l2} ≃-≡ (λ{x} → ≃-refl{x})

varsub-++-commute : ∀{l1 l2 : 𝕃 V} →
                    varsub (l1 ++ l2) (l2 ++ l1) ≡ tt 
varsub-++-commute{l1}{l2} = isSublist-++-commute{V}{_≃_}{l1}{l2} (λ{x} → ≃-refl{x})

varsub-refl : ∀{l : 𝕃 V} → varsub l l ≡ tt 
varsub-refl{l} = isSublist-refl{eq = _≃_} (λ{x} → ≃-refl{x}) {l}

varsub-remove-both : ∀{l1 l2 : 𝕃 V}{a : V} →
                     varsub l1 l2 ≡ tt →
                     varsub (varrem a l1) (varrem a l2) ≡ tt
varsub-remove-both{l1}{l2}{a} = isSublist-remove-both{eq = _≃_}{l1}{l2}{a} (λ{x} → ≃-sym{x}) ≃-≡

varrem-commute : ∀{x1 x2 : V}{xs : 𝕃 V} →
                 varrem x1 (varrem x2 xs) ≡ varrem x2 (varrem x1 xs)
varrem-commute{x1}{x2}{xs} = remove-commute{eq = _≃_} {x1}{x2}{xs}

varrem-++ : ∀{l1 l2 : 𝕃 V}{x : V} →
             varrem x (l1 ++ l2) ≡ varrem x l1 ++ varrem x l2
varrem-++{l1}{l2}{x} = remove-++ _≃_ x l1 l2

varsub-remove2 : ∀{l1 l2 : 𝕃 V}{a : V} →
                 varsub l1 l2 ≡ tt →
                 varsub (varrem a l1) l2 ≡ tt
varsub-remove2{l1}{l2}{a} sb = isSublist-remove2{eq = _≃_}{l1}{l2}{a} (λ{x} → ≃-sym{x}) sb

varapart-[] : ∀{l : 𝕃 V} → varapart l [] ≡ tt
varapart-[]{l} = disjoint-[]{V}{l}{_≃_}

varapart-++ : ∀{l1 l2a l2b : 𝕃 V}→
               varapart l1 (l2a ++ l2b) ≡ tt →
               varapart l1 l2a ≡ tt ∧ varapart l1 l2b ≡ tt
varapart-++{l1}{l2a}{l2b} = disjoint-++{V}{l1}{l2a}{l2b}{_≃_}

varapart-++i : ∀{l1 l2 l3 : 𝕃 V} →
              varapart l1 l2 ≡ tt →
              varapart l1 l3 ≡ tt →
              varapart l1 (l2 ++ l3) ≡ tt
varapart-++i{l1}{l2}{l3} = disjoint-++i{V}{l1}{l2}{l3}{_≃_}

varapart-++2 : ∀{l1a l1b l2 : 𝕃 V} →
               varapart (l1a ++ l1b) l2 ≡ tt →
               varapart l1a l2 ≡ tt ∧ varapart l1b l2 ≡ tt
varapart-++2{l1a}{l1b}{l2} = disjoint-++2{V}{l1a}{l1b}{l2}{_≃_}

varmem-++ : ∀(x : V)(l1 l2 : 𝕃 V) →
            varmem x (l1 ++ l2) ≡ varmem x l1 || varmem x l2
varmem-++ x l1 l2 = list-member-++ _≃_ x l1 l2

~varmem-:: : ∀{x y : V}{vs : 𝕃 V} →
             ~ varmem x (y :: vs) ≡ tt →
             ~ varmem x vs ≡ tt
~varmem-::{x}{y}{vs} e rewrite varmem-++ x [ y ] vs = ~||-elim2{x ≃ y || ff} e

varmem-remove : ∀{x y : V}{l : 𝕃 V} →
                varmem x (varrem y l) ≡ tt →
                x ≃ y ≡ ff ∧ varmem x l ≡ tt
varmem-remove{x}{y}{l} = list-member-remove{eq = _≃_}{x}{y}{l} ≃-≡ (λ{x} → ≃-sym{x}) (λ{x} → ≃-refl{x})

varmem-remove2 : ∀{x y : V}{l : 𝕃 V} →
                 varmem x (varrem y l) ≡ ff →
                 x ≃ y ≡ tt ∨ varmem x l ≡ ff
varmem-remove2{x}{y}{l} = list-member-remove2{V}{_≃_}{x}{y}{l} ≃-≡

varmem-remove2a : ∀{x y : V}{l : 𝕃 V} →
                 varmem x (varrem y l) ≡ ff →
                 x ≃ y ≡ tt ∨ (x ≃ y ≡ ff ∧ varmem x l ≡ ff)
varmem-remove2a{x}{y}{l} u with keep (x ≃ y)
varmem-remove2a{x}{y}{l} u | tt , eq = inj₁ eq
varmem-remove2a{x}{y}{l} u | ff , eq with varmem-remove2{x}{y}{l} u
varmem-remove2a{x}{y}{l} u | ff , eq | inj₁ i rewrite i with eq 
varmem-remove2a{x}{y}{l} u | ff , eq | inj₁ i | () 
varmem-remove2a{x}{y}{l} u | ff , eq | inj₂ i = inj₂ (eq , i)

varmem-remove3 : ∀{x y : V}{l : 𝕃 V} →
                 x ≃ y ≡ ff →
                 varmem x l ≡ tt →
                 varmem x (varrem y l) ≡ tt
varmem-remove3{x}{y}{l} u v rewrite remove-not-member{V}{_≃_}{l}{y}{x} (λ{x} → ≃-sym{x}) ≃-≡  (~≃-sym{x} u) = v 
                 
varmem-remove4 : ∀{x y : V}{l : 𝕃 V} →
                 x ≃ y ≡ ff →
                 varmem x l ≡ ff →
                 varmem x (varrem y l) ≡ ff
varmem-remove4{x}{y}{l} u v rewrite remove-not-member{V}{_≃_}{l}{y}{x} (λ{x} → ≃-sym{x}) ≃-≡  (~≃-sym{x} u) = v 

varmem-remove-neq : ∀{x y : V}{l : 𝕃 V} →
                     x ≃ y ≡ ff →
                     varmem x (varrem y l) ≡ varmem x l
varmem-remove-neq{x}{y}{l} = list-member-neq{V}{_≃_}{x}{y}{l} ≃-≡ (λ{x} → ≃-sym{x}) (λ{x} → ≃-refl{x})

varrem-not-member : ∀{x : V}{l : 𝕃 V} →
                    varmem x l ≡ ff →
                    varrem x l ≡ l
varrem-not-member{x}{l} m = remove-not-member1{V}{_≃_}{l}{x} (λ{x} → ≃-sym{x}) ≃-≡ m

varmem-remove-same : ∀{x : V}{l : 𝕃 V} →
                     varmem x (varrem x l) ≡ ff
varmem-remove-same{x}{l} = list-member-remove-same{V}{_≃_}{x}{l}

varapart-varsub : ∀{l1 l1' l2 l2' : 𝕃 V} →
                   varsub l1 l1' ≡ tt →
                   varsub l2 l2' ≡ tt →                    
                   varapart l1' l2' ≡ tt →
                   varapart l1 l2 ≡ tt
varapart-varsub{l1}{l1'}{l2}{l2'} =                    
   disjoint-sublist{V}{_≃_}{l1}{l1'}{l2}{l2'} ≃-≡ (λ{x} → ≃-sym{x})

varapart-sym : ∀{l1 l2 : 𝕃 V } →
              varapart l1 l2 ≡ tt →
              varapart l2 l1 ≡ tt
varapart-sym{l1}{l2} = disjoint-sym{V}{l1}{l2}{_≃_} (λ{x} → ≃-sym{x})

varmem-varsub : ∀{x : V}{l1 l2 : 𝕃 V} →
                varmem x l1 ≡ tt →
                varsub l1 l2 ≡ tt →
                varmem x l2 ≡ tt
varmem-varsub{x}{l1}{l2} = list-member-sub{V}{_≃_}{x}{l1}{l2} ≃-≡

varmem-varsub-ff : ∀{a : V}{l1 l2 : 𝕃 V} →
                 varsub l1 l2 ≡ tt →
                 varmem a l2 ≡ ff →
                 varmem a l1 ≡ ff
varmem-varsub-ff{a}{l1}{l2} = list-member-sub-ff{V}{_≃_}{a}{l1}{l2} ≃-≡

varsub-remove : ∀{l1 l2 : 𝕃 V}{a : V} →
                varsub (varrem a l1) l2 ≡ tt →
                varsub l1 (a :: l2) ≡ tt
varsub-remove{l1}{l2}{a} = isSublist-remove{V}{_≃_}{l1}{l2}{a} (λ{x} → ≃-sym{x})

varsub-remove1 : ∀{l1 l2 : 𝕃 V}{a : V} →
                  varsub l1 (a :: l2) ≡ tt →
                  varsub (varrem a l1) l2 ≡ tt 
varsub-remove1{l1}{l2}{a} sb = isSublist-remove1{V}{_≃_}{l1}{l2}{a} (λ{x} → ≃-sym{x}) sb

varsub-++ : ∀{l1 l2 l3 : 𝕃 V} →
            varsub (l1 ++ l2) l3 ≡ varsub l1 l3 && varsub l2 l3
varsub-++{l1}{l2}{l3} = list-all-append (λ a → varmem a l3) l1 l2

varunique-++1 : ∀{l1 l2 : 𝕃 V} →
                varunique (l1 ++ l2) ≡ tt →
                varunique l1 ≡ tt
varunique-++1{l1}{l2} = unique-++1{V}{_≃_}{l1}{l2} 

varunique-++2 : ∀{l1 l2 : 𝕃 V} →
                varunique (l1 ++ l2) ≡ tt →
                varunique l2 ≡ tt
varunique-++2{l1}{l2} = unique-++2{V}{_≃_}{l1}{l2}

varunique-++-varapart : ∀{l1 l2 : 𝕃 V} →
                        varunique (l1 ++ l2) ≡ tt →
                        varapart l1 l2 ≡ tt 
varunique-++-varapart{l1}{l2} = unique-++-disjoint{V}{_≃_}{l1}{l2}

varapart-++-varunique : ∀{l1 l2 : 𝕃 V} →
                        varapart l1 l2 ≡ tt →
                        varunique l1 ≡ tt →
                        varunique l2 ≡ tt →                         
                        varunique (l1 ++ l2) ≡ tt 
varapart-++-varunique{l1}{l2} = disjoint-++-unique{V}{_≃_}{l1}{l2}


