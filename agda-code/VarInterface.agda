open import lib
open import bool-relations

fresh-distinctness : ∀{V : Set}(_≃_ : V → V → 𝔹) → (𝕃 V → V) → Set
fresh-distinctness{V} _≃_ fresh = ∀ {l : 𝕃 V} → list-member _≃_ (fresh l) l ≡ ff

fresh-extending : ∀{V : Set}(_≃_ : V → V → 𝔹) → (𝕃 V → V) → Set
fresh-extending{V} _≃_ fresh = ∀{x : V}{l1 l2 : 𝕃 V} → fresh l2 ≃ fresh (x :: l1 ++ l2) ≡ ff

record VI : Set₁ where
  field
    V : Set
    _≃_ : V → V → 𝔹
    ≃-equivalence : equivalence _≃_
    ≃-≡ : ∀ {x y : V} → x ≃ y ≡ tt → x ≡ y

  field
    fresh : 𝕃 V → V
    fresh-distinct : fresh-distinctness _≃_ fresh
    fresh-extend : fresh-extending _≃_ fresh

  fresh2 : V → V → V
  fresh2 v v' = fresh (v :: [ v' ])

  ≃-refl = fst (fst ≃-equivalence)
  ≃-sym = snd ≃-equivalence
  ≃-trans = snd (fst ≃-equivalence)
  ~≃-sym = ~symmetric _≃_ ≃-sym
  ~≃-sym2 = ~symmetric2 _≃_ ≃-sym

  ¬≃ : ∀{x y : V} → ¬ (x ≃ y ≡ tt) → x ≃ y ≡ ff 
  ¬≃{x}{y} p with x ≃ y 
  ¬≃{x}{y} p | tt with (p refl)
  ¬≃{x}{y} p | tt | ()
  ¬≃{x}{y} p | ff = refl


  ≃-⊥ : ∀{x : V} → (x ≃ x) ≡ ff → ∀{X : Set} → X
  ≃-⊥{x} u rewrite ≃-refl{x} with u
  ≃-⊥{x} u | ()

  ≃-uip : ∀{x y : V}{b : 𝔹}(p q : x ≃ y ≡ b) → p ≡ q
  ≃-uip{x}{y} p q with x ≃ y 
  ≃-uip{x}{y} refl refl | u = refl

  fresh-distinct-in : ∀{x : V}{vs : 𝕃 V} →
                       list-in x vs →
                       fresh vs ≃ x ≡ ff
  fresh-distinct-in {x}{vs} I with list-in-member{eq = _≃_} (≃-refl{x}) I | fresh-distinct{vs}
  fresh-distinct-in {x}{vs} I | M | D = ~≃-sym (member-in-out{l = vs} ≃-≡ M D)

----------------------------------------------------------------------
-- an implementation of the above interface based on V = ℕ

s+ : ℕ → ℕ → ℕ
s+ x y = suc (x + y)

fresh-ℕ : 𝕃 ℕ → ℕ
fresh-ℕ l = (foldr s+ 0 l)

fresh-ℕ-step : ∀{x : ℕ}{l1 l2 : 𝕃 ℕ} → x < fresh-ℕ (l1 ++ x :: l2) ≡ tt
fresh-ℕ-step {x} {[]}{l2} = <+3{x}{suc x}{fresh-ℕ l2} (<-suc x)
fresh-ℕ-step {x} {x₁ :: l1}{l2} with fresh-ℕ-step{x}{l1}{l2}
fresh-ℕ-step {x} {y :: l1}{l2} | r = <+1 {x} {suc y} {fresh-ℕ (l1 ++ x :: l2)} (fresh-ℕ-step{x}{l1}{l2}) 

fresh-ℕ-distinct : ∀{l1 l2 : 𝕃 ℕ} →
                   list-member _=ℕ_ (fresh-ℕ (l1 ++ l2)) l2 ≡ ff
fresh-ℕ-distinct {l1}{[]} = refl
fresh-ℕ-distinct {l1}{x :: l2} rewrite =ℕ-sym (fresh-ℕ (l1 ++ x :: l2)) x | (<-not-=ℕ'{x} (fresh-ℕ-step{x}{l1}{l2})) |
  sym (++-singleton x l1 l2) =
  fresh-ℕ-distinct{l1 ++ [ x ]}{l2}

fresh-ℕ-extendh : ∀{x : ℕ}{l1 l2 : 𝕃 ℕ} → fresh-ℕ l2 < fresh-ℕ (x :: l1 ++ l2) ≡ tt
fresh-ℕ-extendh {x} {[]} {l2} rewrite sym (+suc x (fresh-ℕ l2)) = <+1 {fresh-ℕ l2} {x} {suc (fresh-ℕ l2)} (<-suc (fresh-ℕ l2))
fresh-ℕ-extendh {x} {y :: l1} {l2} = <+1 {fresh-ℕ l2} {suc x} {fresh-ℕ (y :: l1 ++ l2)} (fresh-ℕ-extendh{y}{l1}{l2})

fresh-ℕ-extend : fresh-extending{ℕ} _=ℕ_ fresh-ℕ
fresh-ℕ-extend{x}{l1}{l2} rewrite sym (+suc x (fresh-ℕ (l1 ++ l2))) = <-not-=ℕ' {fresh-ℕ l2} {x + suc (fresh-ℕ (l1 ++ l2))} h
  where
    h : fresh-ℕ l2 < x + suc (fresh-ℕ (l1 ++ l2)) ≡ tt
    h rewrite +suc x (fresh-ℕ (l1 ++ l2)) = fresh-ℕ-extendh{x}{l1}{l2}

VI-ℕ : VI
VI-ℕ = record {
        V = ℕ ;
        _≃_ = _=ℕ_ ;
        ≃-equivalence = =ℕ-equivalence ;
        ≃-≡ = =ℕ-to-≡ ;
        fresh = fresh-ℕ ;
        fresh-distinct = λ {l2} → fresh-ℕ-distinct{[]}{l2} ;
        fresh-extend = λ{x}{l1}{l2} → fresh-ℕ-extend{x}{l1}{l2}
        }

open VI VI-ℕ public

remove-fresh1 : ∀{vs : 𝕃 V} → remove _≃_ (fresh vs) (fresh vs :: vs) ≡ vs
remove-fresh1{vs} rewrite ≃-refl{fresh vs}
                | remove-not-member1{eq = _≃_}{vs}{fresh vs} (λ{a} → ≃-sym{a}) ≃-≡ (fresh-distinct{vs})= refl

varmem : V → 𝕃 V → 𝔹
varmem x vs = list-member _≃_ x vs

varsub : 𝕃 V → 𝕃 V → 𝔹
varsub vs vs' = isSublist vs vs' _≃_

varapart : 𝕃 V → 𝕃 V → 𝔹
varapart vs vs' = disjoint _≃_ vs vs' 

varrem : V → 𝕃 V → 𝕃 V
varrem = remove _≃_

varsub-++il : ∀{l1 l2 l3 : 𝕃 V} →
                varsub l1 l3 ≡ tt →
                varsub l2 l3 ≡ tt →
                varsub (l1 ++ l2) l3 ≡ tt
varsub-++il{l1}{l2}{l3} = isSublist-++il{eq = _≃_}{l1}{l2}{l3} 

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

varsub-++2a : ∀ {l1 l2 : 𝕃 V} →
             varsub l2 (l1 ++ l2) ≡ tt
varsub-++2a{l1}{l2} = isSublist-++2a{eq = _≃_} {l1}{l2} (λ{x} → ≃-refl{x})


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

varapart-++i : ∀{l1 l2 l3 : 𝕃 V} →
              varapart l1 l2 ≡ tt →
              varapart l1 l3 ≡ tt →
              varapart l1 (l2 ++ l3) ≡ tt
varapart-++i{l1}{l2}{l3} = disjoint-++i{V}{l1}{l2}{l3}{_≃_}