{-# OPTIONS --allow-unsolved-metas #-}
open import lib
open import VarInterface

module TriangleLemmas where

open import Tm 
open import Subst
open import Apart
open import Alpha
open import Renaming
open import Substitution hiding (_\\_)
open import AlphaCanon
open import Takahashi 
open import Parallel

all-to-pathDistinct-tk : ∀{vs : 𝕃 V}{t : Tm} →
                         allDistinct vs t ≡ tt →
                         pathDistinct vs (tk t) ≡ tt 
all-to-pathDistinct-tk{vs}{t} ad =
 ⇒αβ-all-to-path{t}{tk t}{tt}{vs} refl ad (pathDistinct-tk {t} {vs} (all-to-path{t} ad)) 

applyr-⇒αβ : ∀{r s : Tm}{ρ : Renaming}{b : 𝔹} →
             pathDistinct (ranr ρ) s ≡ tt →
             r ⟨ ⇒αβ b ⟩ s →
             applyr ρ r ⟨ ⇒αβ b ⟩ applyr ρ s
applyr-⇒αβ {r} {s} {ρ} {b} ap var = var
applyr-⇒αβ {r} {s} {ρ} {b} ap (app d1 d2) = {!!}
applyr-⇒αβ {r} {s} {ρ} {b} ap (beta d1 d2 sb) = {!!}
applyr-⇒αβ {ƛ x r} {ƛ y s} {ρ} {ff} ap (alpha{t' = t'}{b = b'} nf ne d sb) =
 alpha {x} {y} {applyr (ρ \\ x) r} {applyr (ρ \\ x) t'} {applyr (ρ \\ y) s} {b'}
  (applyr-∈ {y} {ρ \\ x} {t'} h nf) ne (applyr-⇒αβ {r} {t'} {ρ \\ x} {b'} {!!} d) {!!}
 where h : ~ varmem y (x :: ranr ρ) ≡ tt
       h rewrite ~≃-sym{x} ne = &&-elim1 ap
applyr-⇒αβ {ƛ x r} {ƛ x s} {ρ} {b} ap (lam d) = lam (applyr-⇒αβ{r}{s}{ρ \\ x} (&&-elim2 ap) d)

Alpha-⇒αβ : ∀{ρ : Renaming}{r s t : Tm}{b : 𝔹} →
            Alpha ρ r s →
            s ⟨ ⇒αβ b ⟩ t →
            applyr ρ r ⟨ ⇒αβ ff ⟩ t
Alpha-⇒αβ {ρ} {r} {s} {t} {b} (var u) var rewrite u = var
Alpha-⇒αβ {ρ} {r1 · r2} {s1 · s2} {t1 · t2} {b} (app h1 h2) (app{b1 = b1}{b2} d1 d2) =
  app (Alpha-⇒αβ {ρ} {r1} {s1} {t1} {b1} h1 d1)
      (Alpha-⇒αβ {ρ} {r2} {s2} {t2} {b2} h2 d2)
Alpha-⇒αβ {ρ} {(ƛ y r1) · r2} {ƛ x s1 · s2} {t} {b} (app (lam nf ne h1) h2) (beta{t1' = t2}{t1}{b1 = b1}{b2} d1 d2 sb) =
 beta{applyr ρ r2}{y}{applyr (ρ \\ y) r1}{t2}{applyr [ x , y ] t1}{t}{ff}{ff}
    (Alpha-⇒αβ{ρ}{r2}{s2}{t2}{b1} h2 d1)
    {!h!}
    {!!} -- (Alpha-⇒αβ{ρ \\ y}{r1}{s1}{t1}{b2} {!!} d2) {!!}
 where h : applyr (ρ \\ y) r1 ⟨ ⇒αβ ff ⟩ applyr [ x , y ] t1
       h = {!!} 
Alpha-⇒αβ {ρ} {r} {s} {t} {b} h (alpha x x₁ x₂ x₃) = {!!}
Alpha-⇒αβ {ρ} {r} {s} {t} {b} h (lam x) = {!!}

Subst-var-tk : ∀{s r : Tm}{x y : V}{vs : 𝕃 V} →
               varmem x (bvs s) ≡ ff →
               varmem y (bvs s) ≡ ff →                
               varsub (fvs s) vs ≡ tt → 
               allDistinct vs s ≡ tt → 
               Subst (var x) y s r →
               Subst (var x) y (tk s) (tk r)
Subst-var-tk {var z} {r} {x} {y} {vs} nx ny vf ad var-found = var-found
Subst-var-tk {var z} {r} {x} {y} {vs} nx ny vf ad (var-not x₂) = var-not x₂
Subst-var-tk {s1 · s2} {r1 · r2} {x} {y} {vs} nx ny vf ad (app sb1 sb2)
 rewrite varmem-++ x (bvs s1) (bvs s2) | varmem-++ y (bvs s1) (bvs s2)
 with Subst-var-tk {s1} {r1} {x} {y}{vs}
        (fst (||-≡-ff{varmem x (bvs s1)} nx)) (fst (||-≡-ff{varmem y (bvs s1)} ny))
        (varsub-++1l{fvs s1}{fvs s2}{vs} vf) (allDistinct-app1{s1}{s2}{vs} ad) sb1
    | Subst-var-tk {s2} {r2} {x} {y}{vs} 
        (snd (||-≡-ff{varmem x (bvs s1)} nx)) (snd (||-≡-ff{varmem y (bvs s1)} ny))
        (varsub-++2l{fvs s1}{fvs s2}{vs} vf) (allDistinct-app2{s1}{s2}{vs} ad) sb2 
Subst-var-tk {var z · s2} {r1 · r2} {x} {y} {vs} nx ny vf ad (app var-found sb2) | p1 | p2 = app var-found p2
Subst-var-tk {var z · s2} {r1 · r2} {x} {y} {vs} nx ny vf ad (app (var-not ne) sb2) | p1 | p2 = app (var-not ne) p2
Subst-var-tk {sa · sb · s2} {r1 · r2} {x} {y} {vs} nx ny vf ad (app (app sba sbb) sb2) | p1 | p2 = app p1 p2
Subst-var-tk {(ƛ z s1) · s2} {r1 · r2} {x} {y} {vs} nx ny vf ad (app (lam-stop ne) sb2) | p1 | p2 =
 Subst-var-graft1 {tk s2} {tk s1} {tk r2} {tk s1} {x} {y} {z} {z :: vs}
  (fst (||-≡-ff{x ≃ z} (fst (||-≡-ff{varmem x (bvs (ƛ z s1))} nx))))
  (fst (||-≡-ff{y ≃ z} (fst (||-≡-ff{varmem y (bvs (ƛ z s1))} ny))))
  (varmem-varsub-ff {x} {bvs (tk s1)} {bvs s1} (varsub-bvs-tk{s1})
    (snd (||-≡-ff{x ≃ z} (fst (||-≡-ff{x ≃ z || varmem x (bvs s1)} nx)))))
  (varmem-varsub-ff {y} {bvs (tk s1)} {bvs s1} (varsub-bvs-tk{s1})
    (snd (||-≡-ff{y ≃ z} (fst (||-≡-ff{y ≃ z || varmem y (bvs s1)} ny)))))
  (varsub-trans {fvs (tk s2)} {fvs s2} {z :: vs}
    (varsub-fvs-tk{s2})
    (varsub-trans {fvs s2} {vs} {z :: vs} h'
      (varsub-++2a{[ z ]}{vs})))
      (all-to-pathDistinct-tk {z :: vs} {s1}
       (snd (allDistinct-lam{z}{s1}{vs} (allDistinct-app1{ƛ z s1}{s2}{vs} ad))))
  p2
  (Subst-refl {var x} {tk s1} {y} (h ny))
  where h : (y =ℕ z || list-member _=ℕ_ y (bvs s1)) ||
            list-member _=ℕ_ y (bvs s2)
            ≡ ff → varmem y (fvs (tk s1)) ≡ ff
        h u with ∈ƛff{y}{z}{s1} ne 
        h u | inj₁ i rewrite i with u
        h u | inj₁ i | ()
        h u | inj₂ (_ , i) = varmem-varsub-ff {y} {fvs (tk s1)} {fvs s1} (varsub-fvs-tk{s1}) i 
        h' : varsub (fvs s2) vs ≡ tt
        h' = varsub-++2l{varrem z (fvs s1)}{fvs s2}{vs}
               (&&-elim2{~ list-member _=ℕ_ z vs && list-all (λ x₁ → ~ list-member _=ℕ_ x₁ vs) (bvs s1 ++ bvs s2)}
                 (&&-elim2{~ list-member _=ℕ_ z (bvs s1 ++ bvs s2) && unique _=ℕ_ (bvs s1 ++ bvs s2)} ad))

Subst-var-tk {(ƛ z s1) · s2} {(ƛ z r1) · r2} {x} {y} {vs} nx ny vf ad (app (lam-go ni nc sb1) sb2) | p1 | p2 =
  let adlam = snd (allDistinct-lam{z}{s1}{vs} (allDistinct-app1{ƛ z s1}{s2}{vs} ad)) in
  let xbvs = snd (||-≡-ff{x ≃ z} (fst (||-≡-ff{x ≃ z || varmem x (bvs s1)} nx))) in
  let ybvs = snd (||-≡-ff{y ≃ z} (fst (||-≡-ff{y ≃ z || varmem y (bvs s1)} ny))) in
  let s2vs = varsub-++2l {varrem z (fvs s1)} {fvs s2} {vs} vf in
   Subst-var-graft1 {tk s2} {tk s1} {tk r2} {tk r1} {x} {y} {z}
    {z :: vs}
    (~≃-sym{z} (fst (||-≡-ff{z ≃ x} nc)))
    (fst (∈ƛ{y}{z}{s1} ni))
    (varmem-varsub-ff {x} {bvs (tk s1)} {bvs s1} (varsub-bvs-tk{s1}) xbvs)
    (varmem-varsub-ff {y} {bvs (tk s1)} {bvs s1} (varsub-bvs-tk{s1}) ybvs)
    (  (varsub-trans {fvs (tk s2)} {fvs s2} {z :: vs}
    (varsub-fvs-tk{s2})
    (varsub-trans {fvs s2} {vs} {z :: vs} s2vs
      (varsub-++2a{[ z ]}{vs}))))
    (all-to-pathDistinct-tk {z :: vs} {s1} adlam)
    p2
    (Subst-var-tk {s1} {r1} {x} {y} {z :: vs}
     xbvs
     ybvs
     (varsub-++1l{fvs s1}{fvs s2}{z :: vs}
       (varsub-++il {fvs s1} {fvs s2} {z :: vs}
         (varsub-remove {fvs s1} {vs} {z}
           (varsub-++1l {varrem z (fvs s1)} {fvs s2} {vs} vf))
         (varsub-++2{[ z ]}{fvs s2}{vs} s2vs)))
     adlam
     sb1)

Subst-var-tk {ƛ z s} {ƛ z r} {x} {y} {vs} nx ny vf ad (lam-go w x₃ sb) with keep (y ∈ ƛ z (tk s))
Subst-var-tk {ƛ z s} {ƛ z r} {x} {y} {vs} nx ny vf ad (lam-go w x₃ sb) | tt , eq = 
  lam-go eq x₃
   (Subst-var-tk{s}{r}{x}{y}{z :: vs}
     (snd (||-≡-ff{x ≃ z} nx)) (snd (||-≡-ff{y ≃ z} ny))
     (varsub-remove{fvs s}{vs}{z} vf) (snd (allDistinct-lam{z}{s}{vs} ad)) sb)

Subst-var-tk {ƛ z s} {ƛ z r} {x} {y} {vs} nx ny vf ad (lam-go w x₃ sb) | ff , eq
  with varmem-remove{y}{z}{fvs s} w | varmem-remove2{y}{z}{fvs (tk s)} eq
Subst-var-tk {ƛ z s} {ƛ z r} {x} {y} {vs} nx ny vf ad (lam-go w x₃ sb) | ff , eq | q1 , q2 | inj₁ i rewrite i with q1
Subst-var-tk {ƛ z s} {ƛ z r} {x} {y} {vs} nx ny vf ad (lam-go w x₃ sb) | ff , eq | q1 , q2 | inj₁ i | ()
Subst-var-tk {ƛ z s} {ƛ z r} {x} {y} {vs} nx ny vf ad (lam-go w x₃ sb) | ff , eq | q1 , q2 | inj₂ i = h'
  where h : tk s ≡ tk r
        h = Subst-not-found{var x}{tk s}{tk r}{y}
             (Subst-var-tk{s}{r}{x}{y}{z :: vs}
               (snd (||-≡-ff{x ≃ z} nx))
               (snd (||-≡-ff{y ≃ z} ny))
               (varsub-remove{fvs s}{vs}{z} vf)
               (snd (allDistinct-lam{z}{s}{vs} ad)) sb) i 
        h1 : y ∈ ƛ z (tk r) ≡ ff
        h1 rewrite sym h = eq
        h' : Subst (var x) y (ƛ z (tk s)) (ƛ z (tk r))
        h' rewrite h = lam-stop {var x} {y} {z} {tk r} h1

Subst-var-tk {ƛ z s} {r} {x} {y} {vs} nx ny vf ad (lam-stop w) = lam-stop (∈ƛ-tk-ff{y}{z}{s} w)