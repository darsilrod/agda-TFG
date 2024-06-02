{-# OPTIONS --without-K --exact-split --auto-inline #-}
module Decidability where

open import MLTT renaming (_+_ to _⊕_)
open import Arithmetic


-- Algunas propiedades sobre tipos decidibles

if_then_else_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
    → decidable A → B → B → B
if inl _ then b₁ else _ = b₁
if inr _ then _ else b₂ = b₂

pattern yes x = inl x
pattern no  x = inr x

case-yes : {A : 𝓤 ̇ } → (x : decidable A) → A
    → Σ p ꞉ A , x ＝ yes p
case-yes (yes x) a = x , refl (yes x)
case-yes (no  x) a = !𝟘 _ (x a)

case-no : {A : 𝓤 ̇ } → (x : decidable A) → ¬ A
    → Σ p ꞉ ¬ A , x ＝ no p
case-no (yes x) a = !𝟘 _ (a x)
case-no (no  x) a = x , refl (no x)

b-or-b-then-b : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
    → (p : decidable A) → (b : B)
    → if p then b else b ＝ b 
b-or-b-then-b (yes _) b = refl b
b-or-b-then-b (no _)  b = refl b

dec-eq-of-equiv : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A ≃ B → has-decidable-equality A → has-decidable-equality B 
dec-eq-of-equiv (f , (g₁ , p₁) , (g₂ , p₂)) decA b₁ b₂ = cases-decA (decA (g₁ b₁) (g₁ b₂)) where
    cases-decA : decidable (g₁ b₁ ＝ g₁ b₂) → decidable (b₁ ＝ b₂)
    cases-decA (yes case-eq) = yes (
        b₁        ＝⟨ (p₁ b₁) ⁻¹ ⟩ 
        f (g₁ b₁) ＝⟨ ap f case-eq ⟩ 
        f (g₁ b₂) ＝⟨ p₁ b₂ ⟩ 
        b₂
        ∎)
    cases-decA (no case-neq) = no λ ff → case-neq (ap g₁ ff )

dec-eq-of-copr : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → has-decidable-equality A → has-decidable-equality B 
    → has-decidable-equality (A ⊕ B)
dec-eq-of-copr pA pB (inl x) (inl x') = dec-to-dec (pA x x') where
    dec-to-dec : decidable (x ＝ x') → decidable (inl x ＝ inl x')
    dec-to-dec (yes x-eq-x') = yes (ap inl x-eq-x')
    dec-to-dec (no x-neq-x') = no λ ff → x-neq-x' (down (Eq-copr-eq (inl x) (inl x') ff))
dec-eq-of-copr pA pB (inl x) (inr y') = no (λ ff → !𝟘 _ (down (Eq-copr-eq (inl x) (inr y') ff)))
dec-eq-of-copr pA pB (inr y) (inl x') = no (λ ff → !𝟘 _ (down (Eq-copr-eq (inr y) (inl x') ff)))
dec-eq-of-copr pA pB (inr y) (inr y') = dec-to-dec (pB y y') where
    dec-to-dec : decidable (y ＝ y') → decidable (inr y ＝ inr y')
    dec-to-dec (yes y-eq-y') = yes (ap inr y-eq-y')
    dec-to-dec (no y-neq-y') = no λ ff → y-neq-y' (down (Eq-copr-eq (inr y) (inr y') ff))

ℕ-ℕ-ℕ-ℕ-ℕ-dec-eq : has-decidable-equality (ℕ ⊕ ℕ ⊕ ℕ ⊕ ℕ ⊕ ℕ)
ℕ-ℕ-ℕ-ℕ-ℕ-dec-eq = dec-eq-of-copr ℕ-has-decidable-equality 
    (dec-eq-of-copr ℕ-has-decidable-equality 
    (dec-eq-of-copr ℕ-has-decidable-equality 
    (dec-eq-of-copr ℕ-has-decidable-equality ℕ-has-decidable-equality)))

if-dec-eqℕ : {A : 𝓤 ̇ } (r r' : ℕ) → (x y : A)
    → if ℕ-has-decidable-equality r r' then x else y ＝ if ℕ-has-decidable-equality (succ r) (succ r') then x else y
if-dec-eqℕ r r' x y = cases-eq (ℕ-has-decidable-equality r r') (refl _) (ℕ-has-decidable-equality (succ r) (succ r')) (refl _) where
    cases-eq : (p : decidable (r ＝ r')) → (ℕ-has-decidable-equality r r' ＝ p) 
            → (q : decidable (succ r ＝ succ r')) → (ℕ-has-decidable-equality (succ r) (succ r') ＝ q) 
            → (if ℕ-has-decidable-equality r r' then x else y) ＝(if ℕ-has-decidable-equality (succ r) (succ r') then x else y)
    cases-eq (yes p) dec-r-r'-p (yes q) dec-sr-sr'-q = 
        if ℕ-has-decidable-equality r r' then x else y
            ＝⟨ ap (if_then x else y) (dec-r-r'-p) ⟩ 
        x
            ＝⟨ ap (if_then x else y) (dec-sr-sr'-q ⁻¹) ⟩ 
        if ℕ-has-decidable-equality (succ r) (succ r') then x else y
        ∎
    cases-eq (yes p) dec-r-r'-p (no nq) dec-sr-sr'-q = !𝟘 _ (nq (ap succ p))
    cases-eq (no np) dec-r-r'-p (yes q) dec-sr-sr'-q = !𝟘 _ (np (succ-injective q))
    cases-eq (no np) dec-r-r'-p (no nq) dec-sr-sr'-q = 
        if ℕ-has-decidable-equality r r' then x else y
            ＝⟨ ap (if_then x else y) (dec-r-r'-p) ⟩ 
        y
            ＝⟨ ap (if_then x else y) (dec-sr-sr'-q ⁻¹) ⟩ 
        if ℕ-has-decidable-equality (succ r) (succ r') then x else y
        ∎


-- decidable-upper-bound-is-decidable : {P : ℕ → 𝓤 ̇ } 
--     → Π n ꞉ ℕ , decidable (P n)    
--     → (m : ℕ) → decidable (Π x ꞉ ℕ , (m ≤ x → P x)) 
--     → decidable (Π x ꞉ ℕ , P x)
-- decidable-upper-bound-is-decidable p-n-dec zero (yes x) = yes λ x₁ → x x₁ *
-- decidable-upper-bound-is-decidable p-n-dec zero (no x) = no (λ x₁ → x (λ x _ → x₁ x))
-- decidable-upper-bound-is-decidable {P = P} p-n-dec (succ m) dec-ub = cases-P-0 (p-n-dec 0) where
--     cases-P-0 : decidable (P 0) → decidable (Π x ꞉ ℕ , P x)
--     cases-P-0 (no x) = no (λ x₁ → x (x₁ 0))
--     cases-P-0 (yes x) = cases-P' (decidable-upper-bound-is-decidable P'-is-dec m P'-ub-dec) where

--         P'-is-dec : Π n ꞉ ℕ , decidable (P (n + 1))
--         P'-is-dec n = p-n-dec (succ n)   

--         P'-ub-dec : decidable (Π x ꞉ ℕ , (m ≤ x → P (x + 1))) 
--         P'-ub-dec = cases-dec-ub dec-ub where
--             lemma : {n : ℕ} → (1 ≤ n) → Σ k ꞉ ℕ , (succ k ＝ n) 
--             lemma {zero} p = !𝟘 _ p
--             lemma {succ n} p = n , (refl _)

--             cases-dec-ub : decidable (Π x ꞉ ℕ , ((m + 1) ≤ x → P x)) → decidable (Π x ꞉ ℕ , (m ≤ x → P (x + 1))) 
--             cases-dec-ub (yes x) = yes λ x₁ x₂ → x (succ x₁) x₂
--             cases-dec-ub (no not-dec) = no λ ff → not-dec (λ n → λ p → transport (λ k → P k) ((pr₂ ∘ lemma) (≤-transitive {1} {succ m} {n} * p)) (ff ((pr₁ ∘ lemma {n}) (≤-transitive-aux 1 (succ m) n * p)) 
--                 (transport (λ k → succ m ≤ k) (pr₂ (lemma (≤-transitive-aux 1 (succ m) n * p)) ⁻¹) p)))

--         cases-P' : decidable (Π x ꞉ ℕ , P (x + 1)) → decidable (Π x ꞉ ℕ , P x)
--         cases-P' (yes f) = yes g where
--             g : (n : ℕ) → P n
--             g zero = x
--             g (succ n) = f n
--         cases-P' (no x) = no (λ x₁ → x (λ x → x₁ (succ x)))

