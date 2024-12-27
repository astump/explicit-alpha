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

suc+ : ℕ → ℕ → ℕ
suc+ x y = suc (x + y)

fresh-ℕ : 𝕃 ℕ → ℕ
fresh-ℕ l = (foldr suc+ 0 l)

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

