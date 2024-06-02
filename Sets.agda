{-# OPTIONS --without-K --exact-split --auto-inline #-}
open import PropTruncations

module Sets(pt : subsingleton-truncations-exist) where

open subsingleton-truncations-exist pt public

open import MLTT
open import List
open import Decidability

𝑺𝒆𝒕 : (A : 𝓤 ̇ ) → (has-decidable-equality A) → 𝓤 ̇ 
𝑺𝒆𝒕 A p = Σ xs ꞉ List A , ∥ has-no-rep p xs ∥ 

set-has-no-rep : {A : 𝓤 ̇ } → {p : has-decidable-equality A} → ((xs , y) : 𝑺𝒆𝒕 A p)
    → has-no-rep p xs
set-has-no-rep {_} {A} {p} (xs , y) = Properties.dec-implies-get-element pt (dec-has-no-rep p xs) y


eq-list-eq-set : {A : 𝓤 ̇ } → {p : has-decidable-equality A} → ((xs , y) : 𝑺𝒆𝒕 A p)
    → ((xs' , y') : 𝑺𝒆𝒕 A p)
    → (xs ＝ xs')
    → (xs , y) ＝ (xs' , y')
eq-list-eq-set {_} {A} {p} (xs , y) (xs' , y') (xs-eq-xs') = pr₁ (pr₂ (pair-eq-is-equiv (xs , y) (xs' , y'))) (xs-eq-xs' , y-eq-y') where
    y-eq-y' : (transport _ xs-eq-xs' y) ＝ y'
    y-eq-y' = ∥∥-is-subsingleton (transport (λ z → ∥ (noRep p z) ＝ z ∥) xs-eq-xs' y) y'


eq-list-eq-set' : {A : 𝓤 ̇ } → {p : has-decidable-equality A} → {(xs , y) : 𝑺𝒆𝒕 A p}
    → (xs' : List A)
    → (xs-eq-xs' : xs ＝ xs')
    → Σ y' ꞉ ∥ has-no-rep p xs' ∥ , (xs , y) ＝ (xs' , y')
eq-list-eq-set' {_} {A} {p} {xs , y} xs' (xs-eq-xs') = y' , pr₁ (pr₂ (pair-eq-is-equiv (xs , y) (xs' , y'))) (xs-eq-xs' , y-eq-y') where
    y' : ∥ has-no-rep p xs' ∥ 
    y' = transport _ xs-eq-xs' y

    y-eq-y' : (transport _ xs-eq-xs' y) ＝ y'
    y-eq-y' = ∥∥-is-subsingleton (transport (λ z → ∥ (noRep p z) ＝ z ∥) xs-eq-xs' y) y'


card : {A : 𝓤 ̇ } → {p : has-decidable-equality A} → 𝑺𝒆𝒕 A p → ℕ
card (xs , y) = len xs

-- 1. Conjunto de A vacío
∅ : (A : 𝓤 ̇ ) → (p : has-decidable-equality A) → 𝑺𝒆𝒕 A p
∅ A p = [] , ∣ []-has-no-rep p ∣

add : {A : 𝓤 ̇ } → {p : has-decidable-equality A} 
    → A → 𝑺𝒆𝒕 A p → 𝑺𝒆𝒕 A p 
add {𝓤} {A} {p} a (xs , y) = (noRep p (a :: xs)) , ∣ noRep-fixed-point p (a :: xs) ∣

_isIn_ : {A : 𝓤 ̇ } → {p : has-decidable-equality A} 
    → A → 𝑺𝒆𝒕 A p → 𝓤₀ ̇ 
_isIn_ {𝓤} {A} {p} a (xs , y) = contains p a xs

-- (2) Todo elemento pertenece al conjunto o no (isIn es decidible)
dec-isIn : {A : 𝓤 ̇ } → {p : has-decidable-equality A} 
    → (a : A) → (S : 𝑺𝒆𝒕 A p ) → decidable (a isIn S)
dec-isIn {𝓤} {A} {p} a (xs , y) = dec-contains p a xs 

-- 2. a isIn ∅ es falso
∅-empty : {A : 𝓤 ̇ } → {p : has-decidable-equality A} → (a : A) → ¬ (a isIn (∅ A p))
∅-empty a = id

-- 3. a isIn (add a S) es verdadero
isIn-after-add : {A : 𝓤 ̇ } → {p : has-decidable-equality A} → (a : A)
    → (S : 𝑺𝒆𝒕 A p) → a isIn (add a S)
isIn-after-add {𝓤} {A} {p} a (xs , y) = cases-contains (dec-contains p a xs) (refl _) where
    cases-contains : (q : decidable (contains p a xs)) → (q ＝ dec-contains p a xs)
        → a isIn (add a (xs , y))
    cases-contains (yes a-in-xs) q-eq-paxs = transport (λ t → contains p a (if t then noRep p xs else (a :: noRep p xs))) q-eq-paxs 
        (transport (contains p a) ((set-has-no-rep (xs , y)) ⁻¹) a-in-xs)
    cases-contains (no a-nin-xs) q-eq-paxs = transport (λ t → contains p a (if t then noRep p xs else (a :: noRep p xs))) q-eq-paxs 
        (transport (if_then 𝟙 else contains p a (noRep p xs)) (pr₂ (case-yes (p a a) (refl a)) ⁻¹) *)

-- 4. a isIn (add b S) es a isIn S, si a ≠ b
isIn-iff-before-add : {A : 𝓤 ̇ } → {p : has-decidable-equality A} → (a : A) → (b : A)
    → (¬ (a ＝ b)) → (S : 𝑺𝒆𝒕 A p) → a isIn (add b S) ＝ a isIn S
isIn-iff-before-add {𝓤} {A} {p} a b a-neq-b (xs , y) = cases-b-in-xs (dec-contains p b xs) (refl _) where
    p-a-b-false : Σ r ꞉ ¬ (a ＝ b) , p a b ＝ no r
    p-a-b-false = case-no (p a b) a-neq-b

    cases-b-in-xs : (q : decidable (contains p b xs)) → (dec-contains p b xs ＝ q)
        → a isIn (add b (xs , y)) ＝ a isIn (xs , y)
    cases-b-in-xs (yes b-in-xs) pbxs-eq-q = 
        a isIn add b (xs , y) 
            ＝⟨ refl _ ⟩ 
        contains p a (noRep p (b :: xs))
            ＝⟨ ap (λ t → contains p a (if t then noRep p xs else (b :: noRep p xs))) pbxs-eq-q ⟩ 
        contains p a (noRep p xs) 
            ＝⟨ ap (contains p a) (set-has-no-rep (xs , y)) ⟩ 
        contains p a xs
        ∎

    cases-b-in-xs (no b-nin-xs) pbxs-eq-q = 
        a isIn add b (xs , y) 
            ＝⟨ refl _ ⟩ 
        contains p a (noRep p (b :: xs))
            ＝⟨ ap (λ t → contains p a (if t then noRep p xs else (b :: noRep p xs))) pbxs-eq-q ⟩ 
        contains p a (b :: noRep p xs)
            ＝⟨ refl _ ⟩ 
        if p a b then 𝟙 else contains p a (noRep p xs)
            ＝⟨ ap (if_then 𝟙 else contains p a (noRep p xs)) (pr₂ (case-no (p a b) (a-neq-b))) ⟩ 
        contains p a (noRep p xs)
            ＝⟨ ap (contains p a) (set-has-no-rep (xs , y)) ⟩ 
        contains p a xs
        ∎


remove : {A : 𝓤 ̇ } → {p : has-decidable-equality A} 
    → A → 𝑺𝒆𝒕 A p → 𝑺𝒆𝒕 A p 
remove {_} {A} {p} a (xs , y) = (remove-first p a xs) , ∣ remove-doesnt-add-rep p a xs (set-has-no-rep ((xs , y))) ∣

-- 5. remove a ­∅ es ∅
remove-empty : {A : 𝓤 ̇ } → {p : has-decidable-equality A} → (a : A)
    → (remove a (∅ A p)) ＝ (∅ A p)
remove-empty {𝓤} {A} {p} a = refl _

-- 6. remove a (add a S) es remove a S
remove-after-add : {A : 𝓤 ̇ } → {p : has-decidable-equality A} → (a : A) → (S : 𝑺𝒆𝒕 A p) 
    → remove a (add a S) ＝ remove a S
remove-after-add {𝓤} {A} {p} a (xs , y) = cases-a-in-S (dec-contains p a xs) (refl _) where

    cases-a-in-S : (q : decidable (contains p a xs)) → (dec-contains p a xs ＝ q) → remove a (add a (xs , y)) ＝ remove a (xs , y)
    cases-a-in-S (yes a-in-xs) dec-eq-q = 
        remove a (add a (xs , y)) 
            ＝⟨ refl _ ⟩ 
        remove a (noRep p (a :: xs) , _) 
            ＝⟨ ap (remove a) (eq-list-eq-set (noRep p (a :: xs) , _) (xs , y) (eq-1 ∙ eq-2)) ⟩ 
        remove a (xs , y)
        ∎ where
        eq-1 : noRep p (a :: xs) ＝ noRep p xs
        eq-1 = ap (if_then noRep p xs else (a :: noRep p xs)) dec-eq-q

        eq-2 : noRep p xs ＝ xs
        eq-2 = set-has-no-rep (xs , y)

    cases-a-in-S (no a-nin-xs) dec-eq-q = 
        remove a (add a (xs , y)) 
            ＝⟨ refl _ ⟩ 
        remove a (noRep p (a :: xs) , _) 
            ＝⟨ ap (remove a) (pr₂ (eq-list-eq-set' (a :: noRep p xs) eq-1)) ⟩ 
        remove a ((a :: noRep p xs) , _)
            ＝⟨ refl _ ⟩ 
        (remove-first p a (a :: noRep p xs)) , _
            ＝⟨ pr₂ (eq-list-eq-set' (noRep p xs) eq-2) ⟩ 
        (noRep p xs) , _
            ＝⟨ pr₂ (eq-list-eq-set' xs eq-3) ⟩ 
        xs , _
            ＝⟨ eq-list-eq-set (xs , _) (remove-first p a xs , _) (eq-4⁻¹ ⁻¹) ⟩ 
        remove-first p a xs , _
        ∎ where

        eq-1 : noRep p (a :: xs) ＝ a :: noRep p xs
        eq-1 = ap (if_then noRep p xs else (a :: noRep p xs)) dec-eq-q

        eq-2 : remove-first p a (a :: noRep p xs) ＝ noRep p xs
        eq-2 = ap (if_then noRep p xs else (a :: remove-first p a (noRep p xs))) (pr₂ (case-yes (p a a) (refl a)))

        eq-3 : noRep p xs ＝ xs
        eq-3 = set-has-no-rep (xs , y)

        eq-4⁻¹ : remove-first p a xs ＝ xs
        eq-4⁻¹ = remove-doesnt-add p a xs a-nin-xs

-- 7. remove a (add b S) es add b (remove a S) si a ≠ b
remove-after-neq-add : {A : 𝓤 ̇ } → {p : has-decidable-equality A} → (a b : A) → (S : 𝑺𝒆𝒕 A p) 
    → ¬ (a ＝ b)
    → remove a (add b S) ＝ add b (remove a S)
remove-after-neq-add {𝓤} {A} {p} a b (xs , y) a-neq-b = cases-b-in-S (dec-contains p b xs) (refl _) where

    cases-b-in-S : (q : decidable (contains p b xs)) → (dec-contains p b xs ＝ q) → remove a (add b (xs , y)) ＝ add b (remove a (xs , y))
    cases-b-in-S (yes b-in-xs) dec-eq-q = eq-list-eq-set (remove a (add b (xs , y))) (add b (remove a (xs , y))) eq-a-b where

        eq-1 : noRep p (b :: xs) ＝ noRep p xs
        eq-1 = ap (if_then noRep p xs else (b :: noRep p xs)) dec-eq-q

        eq-2 : noRep p xs ＝ xs
        eq-2 = set-has-no-rep (xs , y)

        b-in-remove : contains p b (remove-first p a xs)
        b-in-remove = remove-only-removes-single-element p a b xs a-neq-b b-in-xs

        eq-3 : noRep p (b :: (remove-first p a xs)) ＝ noRep p (remove-first p a xs)
        eq-3 = 
            noRep p (b :: (remove-first p a xs))
                ＝⟨ refl _ ⟩ 
            if dec-contains p b (remove-first p a xs) then noRep p (remove-first p a xs) else (b :: noRep p (remove-first p a xs)) 
                ＝⟨ ap (if_then noRep p (remove-first p a xs) else (b :: noRep p (remove-first p a xs))) 
                    (pr₂ (case-yes (dec-contains p b (remove-first p a xs)) b-in-remove)) 
                  ⟩ 
            noRep p (remove-first p a xs)
            ∎

        eq-4 : noRep p (remove-first p a xs) ＝ remove-first p a xs
        eq-4 = remove-doesnt-add-rep p a xs (set-has-no-rep (xs , y))

        eq-a-c : remove-first p a (noRep p (b :: xs)) ＝ remove-first p a xs
        eq-a-c = ap (remove-first p a) (eq-1 ∙ eq-2)

        eq-c-b : noRep p (b :: (remove-first p a xs)) ＝ remove-first p a xs
        eq-c-b = eq-3 ∙ eq-4

        eq-a-b : remove-first p a (noRep p (b :: xs)) ＝ noRep p (b :: (remove-first p a xs))
        eq-a-b = eq-a-c ∙ eq-c-b ⁻¹

    cases-b-in-S (no b-nin-xs) dec-eq-q = eq-list-eq-set (remove a (add b (xs , y))) (add b (remove a (xs , y))) eq-a-b where
        
        eq-1 : noRep p (b :: xs) ＝ b :: xs
        eq-1 = 
            noRep p (b :: xs)
                ＝⟨ refl _ ⟩
            if dec-contains p b xs then noRep p xs else (b :: noRep p xs)
                ＝⟨ ap (if_then noRep p xs else (b :: noRep p xs)) dec-eq-q ⟩ 
            b :: noRep p xs
                ＝⟨ ap (b ::_) (set-has-no-rep (xs , y)) ⟩ 
            b :: xs
            ∎

        eq-2 : remove-first p a (noRep p (b :: xs)) ＝ remove-first p a (b :: xs)
        eq-2 = ap (remove-first p a) eq-1

        eq-3 : remove-first p a (b :: xs) ＝ b :: (remove-first p a xs)
        eq-3 = 
            remove-first p a (b :: xs)
                ＝⟨ refl _ ⟩ 
            if p a b then xs else (b :: remove-first p a xs)
                ＝⟨ ap (if_then xs else (b :: remove-first p a xs)) (pr₂ (case-no (p a b) a-neq-b)) ⟩ 
            b :: remove-first p a xs
            ∎

        b-nin-remove : ¬ (contains p b (remove-first p a xs))
        b-nin-remove ff = b-nin-xs (remove-sublist p b a xs ff)

        eq-4 : noRep p (b :: (remove-first p a xs)) ＝ b :: (noRep p (remove-first p a xs))
        eq-4 = noRep p (b :: (remove-first p a xs))
                ＝⟨ refl _ ⟩ 
            if dec-contains p b (remove-first p a xs) then noRep p (remove-first p a xs) else (b :: noRep p (remove-first p a xs))
                ＝⟨ ap (if_then noRep p (remove-first p a xs) else (b :: noRep p (remove-first p a xs))) 
                    (pr₂ (case-no (dec-contains p b (remove-first p a xs)) b-nin-remove)) 
                  ⟩ 
            b :: (noRep p (remove-first p a xs))
            ∎

        eq-5 : noRep p (remove-first p a xs) ＝ remove-first p a xs
        eq-5 = remove-doesnt-add-rep p a xs (set-has-no-rep (xs , y))

        eq-6 : b :: (noRep p (remove-first p a xs)) ＝ b :: (remove-first p a xs)
        eq-6 = ap (b ::_) eq-5

        eq-a-b : remove-first p a (noRep p (b :: xs)) ＝ noRep p (b :: (remove-first p a xs))
        eq-a-b = eq-2 ∙ eq-3 ∙ eq-6 ⁻¹ ∙ eq-4 ⁻¹