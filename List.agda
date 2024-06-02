{-# OPTIONS --without-K --exact-split --auto-inline #-}
module List where

open import Raise
open import MLTT renaming (_+_ to _⊕_)
open import Arithmetic
open import Decidability

data List (A : 𝓤 ̇ ) : 𝓤 ̇  where
    []   : List A
    _::_ : A → List A → List A 
{-# BUILTIN LIST List #-}
infixr 10 _::_

_concat_ : {A : 𝓤 ̇ } → List A → List A → List A 
[]        concat ys = ys
(x :: xs) concat ys = x :: (xs concat ys)

_concat-[] : {A : 𝓤 ̇ } → (xs : List A) → xs concat [] ＝ xs 
[] concat-[] = refl []
(x :: xs) concat-[] = ap (x ::_) (xs concat-[])
infixr 10 _concat_

concat-associative : {A : 𝓤 ̇ } → (xs ys zs : List A) 
    → xs concat (ys concat zs) ＝ (xs concat ys) concat zs 
concat-associative [] ys zs = refl _
concat-associative (x :: xs) ys zs = 
    (x :: xs) concat (ys concat zs)
        ＝⟨ refl _ ⟩ 
    x :: (xs concat (ys concat zs)) 
        ＝⟨ ap (x ::_) (concat-associative xs ys zs) ⟩ 
    x :: ((xs concat ys) concat zs)
        ＝⟨ refl _ ⟩ 
    ((x :: xs) concat ys) concat zs
    ∎

n-zeros-list : ℕ → List ℕ 
n-zeros-list  0       = []
n-zeros-list (succ n) = 0 :: (n-zeros-list n)

non-empty : {A : 𝓤 ̇ } → List A → 𝓤₀ ̇ 
non-empty []       = 𝟘 
non-empty (x :: _) = 𝟙


data Vect (A : 𝓤 ̇ ) : ℕ → 𝓤 ̇  where
    nil : Vect A 0 
    _++_ : {n : ℕ} → A → Vect A n → Vect A (succ n)
infixr 10 _++_

len : {A : 𝓤 ̇ } → List A → ℕ
len [] = 0
len (x :: xs) = succ (len xs)

len-zeros : (n : ℕ) → len (n-zeros-list n) ＝ n 
len-zeros 0        = refl _ 
len-zeros (succ n) = ap succ (len-zeros n)

concat-zeros : (n m : ℕ) → (n-zeros-list n) concat (n-zeros-list m) ＝ n-zeros-list (n + m) 
concat-zeros  0       m = ap n-zeros-list (Peano.zero+n m) ⁻¹
concat-zeros (succ n) m = ap (0 ::_) (concat-zeros n m) ∙ (ap n-zeros-list (Peano.succ+y n m) ⁻¹)


len-concat-is-sum-len : {A : 𝓤 ̇ } → (xs ys : List A) 
    → len (xs concat ys) ＝ (len xs) + (len ys) 
len-concat-is-sum-len [] ys = (Peano.zero+n (len ys)) ⁻¹
len-concat-is-sum-len (x :: xs) ys = 
    succ (len (xs concat ys)) 
        ＝⟨ ap succ (len-concat-is-sum-len xs ys) ⟩
    succ ((len xs) + (len ys))
        ＝⟨ (Peano.succ+y (len xs) (len ys)) ⁻¹ ⟩ 
    succ (len xs) + len ys
    ∎

-- Vect n es lo mismo que listas de longitud n
vect-n-to-list-n : {A : 𝓤 ̇ } → {n : ℕ} → Vect A n → Σ xs ꞉ List A , len xs ＝ n 
vect-n-to-list-n nil = [] , refl zero
vect-n-to-list-n (x ++ v) = (x :: pr₁ (vect-n-to-list-n v)) , ap succ (pr₂ (vect-n-to-list-n v))

list-n-to-vect-n : {A : 𝓤 ̇ } → {n : ℕ} → Σ xs ꞉ List A , len xs ＝ n → Vect A n
list-n-to-vect-n ([] , len-xs) = transport (Vect _) len-xs nil
list-n-to-vect-n {n = succ n} ((x :: xs) , len-xs) = x ++ (list-n-to-vect-n (xs , succ-injective len-xs))



--

-- NEList : (A : 𝓤 ̇ ) → 𝓤 ̇  
-- NEList A = A × List A 

-- nelist-to-list : {A : 𝓤 ̇ } → NEList A → List A 
-- nelist-to-list (x , xs) = x :: xs

-- nelist-len : {A : 𝓤 ̇ } → NEList A → ℕ 
-- nelist-len xs = len (nelist-to-list xs)

-- first : {A : 𝓤 ̇ } → (xs : NEList A) → A 
-- first = pr₁

-- last' : {A : 𝓤 ̇ } → (xs : NEList A) → {n : ℕ} → (p : n ＝ nelist-len xs) → A 
-- last' xs {0} p = pr₁ xs -- Caso irrelevante
-- last' (x , []) {succ zero} p = x
-- last' (x , (y :: ys)) {succ (succ n)} p = last' (y , ys) (succ-injective p)

-- last : {A : 𝓤 ̇ } → NEList A → A 
-- last xs = last' xs (refl _)

-- Observational equality para listas
EqList : {A : 𝓤 ̇ } → List A → List A → 𝓤 ̇ 
EqList {𝓤} []        []        = raise 𝓤 𝟙
EqList {𝓤} []        (y :: ys) = raise 𝓤 𝟘
EqList {𝓤} (x :: xs) []        = raise 𝓤 𝟘
EqList     (x :: xs) (y :: ys) = (x ＝ y) × EqList xs ys

EqListRefl : {A : 𝓤 ̇ } → (xs : List A) → EqList xs xs 
EqListRefl [] = map-raise *
EqListRefl (x :: xs) = refl x , EqListRefl xs

IdListToEqList : {A : 𝓤 ̇ } → (xs ys : List A)
    → xs ＝ ys → EqList xs ys  
IdListToEqList xs xs (refl xs) = EqListRefl xs

EqList-id : {A : 𝓤 ̇ } (xs ys : List A) → EqList xs ys → xs ＝ ys
EqList-id [] [] p = refl []
EqList-id [] (y :: ys) (map-raise f) = !𝟘 ([] ＝ y :: ys) f
EqList-id (x :: xs) [] (map-raise f) = !𝟘 (x :: xs ＝ []) f
EqList-id (x :: xs) (x :: ys) (refl _ , p-xs-ys) = ap (x ::_) (EqList-id xs ys p-xs-ys)

is-equiv-IdListToEqList : {A : 𝓤 ̇ } → (xs ys : List A)
    → is-equiv (IdListToEqList xs ys)
is-equiv-IdListToEqList xs ys = (EqList-id xs ys , lemma-1 xs ys) , (EqList-id xs ys , lemma-2 xs ys) where

    lemma-1-1 : {A : 𝓤 ̇ } {x : A} {ys zs : List A}
        → (p : ys ＝ zs)
        → IdListToEqList (x :: ys) (x :: zs) (ap (x ::_ ) p) ＝ refl x , IdListToEqList ys zs p
    lemma-1-1 (refl _) = refl _

    lemma-1 : {A : 𝓤 ̇ } → (ys zs : List A) → (x : _) → IdListToEqList ys zs (EqList-id ys zs x) ＝ x
    lemma-1 [] [] (map-raise *) = refl _
    lemma-1 [] (x₁ :: zs) (map-raise x) = !𝟘 _ x
    lemma-1 (x₁ :: ys) [] (map-raise x) = !𝟘 _ x
    lemma-1 (x :: ys) (x :: zs) (refl x , y) = 
            IdListToEqList (x :: ys) (x :: zs) (ap (_::_ x) (EqList-id ys zs y))
                ＝⟨ lemma-1-1 (EqList-id ys zs y) ⟩ 
            refl x , IdListToEqList ys zs (EqList-id ys zs y)
                ＝⟨ lemma-aux (refl x) (lemma-1 ys zs y) ⟩ 
            refl x , y
            ∎ 
        where
        lemma-aux : {A B : 𝓤 ̇ } {y z : B} (x : A) → y ＝ z → (x , y) ＝ (x , z) 
        lemma-aux x = ap (x ,_ )
    
    lemma-2-1 : {A : 𝓤 ̇ } → (ys : List A) → EqList-id ys ys (EqListRefl ys) ＝ refl _ 
    lemma-2-1 [] = refl _
    lemma-2-1 (x :: ys) = ap (ap (x ::_)) (lemma-2-1 ys)

    lemma-2 : {A : 𝓤 ̇ } → (ys zs : List A) → (x : _) → EqList-id ys zs (IdListToEqList ys zs x) ＝ x
    lemma-2 [] [] (refl _) = refl _
    lemma-2 (x :: ys) (x :: ys) (refl (x :: ys)) = lemma-2-1 (x :: ys) 

decidable-EqList : {A : 𝓤 ̇ } → (has-decidable-equality A) → (xs ys : List A) → decidable (EqList xs ys)
decidable-EqList p [] [] = inl (map-raise *)
decidable-EqList p [] (y :: ys) = inr down
decidable-EqList p (x :: xs) [] = inr down 
decidable-EqList p (x :: xs) (y :: ys) = aux (p x y) (decidable-EqList p xs ys) where
    aux : (decidable (x ＝ y)) → (decidable (EqList xs ys)) → decidable (EqList (x :: xs) (y :: ys))
    aux (inl a) (inl b) = inl (a , b)
    aux (inl a) (inr b) = inr (λ x → b (pr₂ x))
    aux (inr a) q₂ = inr (λ x → a (pr₁ x))

decidableIdList : {A : 𝓤 ̇ } → (has-decidable-equality A) → has-decidable-equality (List A)
decidableIdList p = λ xs ys → 
    rl-implication (decidable-iff-decidable (IdListToEqList xs ys , pr₁  (pr₁ (is-equiv-IdListToEqList xs ys )))) 
        (decidable-EqList p xs ys) 


-- Funciones sobre listas

contains : {A : 𝓤 ̇ } → (has-decidable-equality A) → A → List A → 𝓤₀ ̇ 
contains p a []        = 𝟘
contains p a (x :: xs) = if (p a x) then 𝟙 else (contains p a xs)

dec-contains : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (a : A) → (xs : List A) 
    → decidable (contains p a xs)
dec-contains p a [] = inr id
dec-contains p a (x :: xs) = by-cases (p a x) (refl _) where

    by-cases : (q : decidable (a ＝ x)) → (p a x ＝ q)
        → decidable (if p a x then 𝟙 else contains p a xs)
    by-cases (yes eq) q = yes (transport (if_then 𝟙 else contains p a xs) (q ⁻¹) *)
    by-cases (no  eq) q = by-cases' (dec-contains p a xs) where

        by-cases' : (decidable (contains p a xs))
            → decidable (if p a x then 𝟙 else contains p a xs)
        by-cases' (yes r) = yes (transport (if_then 𝟙 else contains p a xs) (q ⁻¹) r)
        by-cases' (no  r) = no (r ∘ (transport (if_then 𝟙 else contains p a xs) q))

add-element-contains : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (x : A) → (xs : List A) 
    → contains p x (x :: xs)
add-element-contains p x xs = cases-contains (dec-contains p x (x :: xs)) where
    cases-contains : (q : decidable (contains p x (x :: xs)))
        → contains p x (x :: xs)
    cases-contains (yes p-cont) = p-cont
    cases-contains (no p-n-cont) = transport (if_then 𝟙 else contains p x xs) (pr₂ p-x-x-holds ⁻¹) * where
        p-x-x-holds : Σ r ꞉ (x ＝ x) , (p x x ＝ yes r)
        p-x-x-holds = case-yes (p x x) (refl x)


if-not-in-head-then-tail : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (x y : A) 
    → (xs : List A) → ¬ (x ＝ y) → (contains p x (y :: xs))
    → contains p x xs
if-not-in-head-then-tail p x y xs x-neq-y p-cont = transport (if_then 𝟙 else contains p x xs) (pr₂ p-x-y-not) p-cont where
    p-x-y-not : Σ r ꞉ ¬ (x ＝ y) , (p x y ＝ no r)
    p-x-y-not = case-no (p x y) x-neq-y

add-does-not-remove-elements : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (x y : A) 
    → (xs : List A) → (contains p x xs) 
    → contains p x (y :: xs)
add-does-not-remove-elements p x y xs x-in-xs = cases-x-eq-y (p x y) (refl _) where
    cases-x-eq-y : (q : decidable (x ＝ y)) → (p x y ＝ q) 
        → contains p x (y :: xs)
    cases-x-eq-y (yes x-eq-y) pxy-eq-q = transport (if_then 𝟙 else contains p x xs) (pxy-eq-q ⁻¹) *
    cases-x-eq-y (no x-neq-y) pxy-eq-q = transport (if_then 𝟙 else contains p x xs) (pxy-eq-q ⁻¹) x-in-xs 

if-not-in-then-not-in-tail : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (x y : A) 
    → (xs : List A) → ¬ (contains p x (y :: xs)) 
    → ¬ (contains p x xs)
if-not-in-then-not-in-tail p x y xs not-in = cases-x-eq-y (p x y) where
    cases-x-eq-y : decidable (x ＝ y)
        → ¬ (contains p x xs)
    cases-x-eq-y (yes x-eq-y) = !𝟘 _ (not-in (transport (λ t → if p t y then 𝟙 else contains p t xs) (x-eq-y ⁻¹) (add-element-contains p y xs)))
    cases-x-eq-y (no x-neq-y) = cases-aux (dec-contains p x xs) where
        cases-aux : decidable (contains p x xs) → ¬ (contains p x xs)
        cases-aux (no x-nin-xs) = x-nin-xs
        cases-aux (yes x-in-xs) = !𝟘 _ (not-in (add-does-not-remove-elements p x y xs x-in-xs ))


noRep : {A : 𝓤 ̇ } → (has-decidable-equality A) → List A → List A
noRep p []        = []
noRep p (x :: xs) = if (dec-contains p x xs) then (noRep p xs) else (x :: noRep p xs)

noRep-does-not-add-elements : {A : 𝓤 ̇ } → (p : has-decidable-equality A) 
    → (x : A) → (xs : List A ) → ¬ (contains p x xs)
    → ¬ (contains p x (noRep p xs))
noRep-does-not-add-elements p x [] q-cont = id
noRep-does-not-add-elements p x (y :: xs) q-cont = cases-equals (p x y) (refl _) where
    cases-equals : (q : decidable (x ＝ y)) → (p x y ＝ q)
        →  ¬ (contains p x (noRep p (y :: xs)))
    cases-equals (yes p-eq) p-eq-q = !𝟘 _ (q-cont (transport (λ t → contains p t (y :: xs)) (p-eq ⁻¹) (add-element-contains p y xs)))
    cases-equals (no p-neq) p-eq-q = cases-y-in-xs (dec-contains p y xs) (refl _) where
        cases-y-in-xs : (r : decidable (contains p y xs)) → (r ＝ dec-contains p y xs)
            → ¬ (contains p x (noRep p (y :: xs)))
        cases-y-in-xs (yes y-in-xs) dec-cont-eq ff = (noRep-does-not-add-elements p x xs 
            (if-not-in-then-not-in-tail p x y xs q-cont))
            (transport (λ t → contains p x(if t then noRep p xs else (y :: noRep p xs))) (dec-cont-eq ⁻¹) ff)
        cases-y-in-xs (no y-nin-xs) dec-cont-eq ff = (noRep-does-not-add-elements p x xs 
            (if-not-in-then-not-in-tail p x y xs q-cont))
            (transport (if_then 𝟙 else contains p x (noRep p xs)) (p-eq-q) 
            (transport (λ t → contains p x(if t then noRep p xs else (y :: noRep p xs))) (dec-cont-eq ⁻¹) ff))

noRep-fixed-point : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (xs : List A )
    → noRep p (noRep p xs) ＝ noRep p xs
noRep-fixed-point p [] = refl _
noRep-fixed-point p (x :: xs) = case-contains (dec-contains p x xs) (refl _) where
    case-contains : (q : decidable (contains p x xs)) → (dec-contains p x xs ＝ q)
        → noRep p (noRep p (x :: xs)) ＝ noRep p (x :: xs)

    case-contains (yes p-cont) p-eq = ap (noRep p) aux-equality-2 
        ∙ (noRep-fixed-point p xs) 
        ∙ (aux-equality-1 ⁻¹) where

            aux-equality-1 : if (dec-contains p x xs) then (noRep p xs) else (x :: noRep p xs) 
                ＝ if (yes p-cont) then (noRep p xs) else (x :: noRep p xs)
            aux-equality-1 = ap (if_then (noRep p xs) else (x :: noRep p xs)) p-eq

            aux-equality-2 : noRep p (x :: xs) ＝ noRep p xs 
            aux-equality-2 = noRep p (x :: xs) 
                    ＝⟨ refl _ ⟩
                if (dec-contains p x xs) then (noRep p xs) else (x :: noRep p xs) 
                    ＝⟨ aux-equality-1 ⟩
                if (yes p-cont) then (noRep p xs) else (x :: noRep p xs)
                    ＝⟨ refl _ ⟩
                noRep p xs 
                ∎ 

    case-contains (no p-cont) p-eq = (ap (noRep p) aux-equality-4) ∙ aux-equality-6 ∙ (aux-equality-4 ⁻¹) where

        aux-equality-3 : if (dec-contains p x xs) then (noRep p xs) else (x :: noRep p xs) 
                ＝ if (no p-cont) then (noRep p xs) else (x :: noRep p xs)
        aux-equality-3 = ap (if_then (noRep p xs) else (x :: noRep p xs)) p-eq 


        aux-equality-4 : noRep p (x :: xs) ＝ x :: noRep p xs
        aux-equality-4 = noRep p (x :: xs) 
                ＝⟨ refl _ ⟩
            if dec-contains p x xs then noRep p xs else (x :: noRep p xs)
                ＝⟨ aux-equality-3 ⟩ 
            if (no p-cont) then noRep p xs else (x :: noRep p xs)
                ＝⟨ refl _ ⟩
            x :: noRep p xs
            ∎

        aux-equality-5 : dec-contains p x (noRep p xs) ＝ no _ 
        aux-equality-5 = pr₂ (cases-dec (dec-contains p x (noRep p xs)) (refl _)) where
            cases-dec : (q : decidable (contains p x (noRep p xs))) → (q ＝ dec-contains p x (noRep p xs))
                → Σ nq ꞉ ¬ (contains p x (noRep p xs)) , dec-contains p x (noRep p xs) ＝ no nq
            cases-dec (yes q) q-eq-dec = !𝟘 _ (noRep-does-not-add-elements p x xs p-cont q)
            cases-dec (no nq) q-eq-dec = nq , (q-eq-dec ⁻¹)

        aux-equality-6 : noRep p (x :: noRep p xs) ＝ x :: noRep p xs
        aux-equality-6 = noRep p (x :: noRep p xs) 
                ＝⟨ refl _ ⟩
            if dec-contains p x (noRep p xs) then noRep p (noRep p xs) else (x :: noRep p (noRep p xs))
                ＝⟨ ap (if_then noRep p (noRep p xs) else (x :: noRep p (noRep p xs))) aux-equality-5 ⟩ 
            x :: noRep p (noRep p xs)
                ＝⟨ ap (x ::_ ) (noRep-fixed-point p xs) ⟩ 
            x :: noRep p xs
            ∎

remove-first : {A : 𝓤 ̇ } →  (has-decidable-equality A) → A → List A → List A
remove-first p a [] = []
remove-first p a (x :: xs) = if (p a x) then xs else (x :: remove-first p a xs)

remove-doesnt-add : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (a : A) → (xs : List A) → ¬ (contains p a xs)
    → remove-first p a xs ＝ xs
remove-doesnt-add p a [] not-contains = refl _
remove-doesnt-add p a (x :: xs) not-contains = cases-pax (p a x) (refl _ ) where
    cases-pax : (q : decidable (a ＝ x)) → (q ＝ p a x) → remove-first p a (x :: xs) ＝ x :: xs
    cases-pax (yes a-eq-x) q-eq-pax = !𝟘 _ (not-contains (transport (λ t → contains p t (x :: xs)) (a-eq-x ⁻¹) (add-element-contains p x xs)))
    cases-pax (no a-neq-x) q-eq-pax = (ap (if_then xs else (x :: remove-first p a xs)) (q-eq-pax ⁻¹) ) 
        ∙ (ap (x ::_) (remove-doesnt-add p a xs (if-not-in-then-not-in-tail p a x xs not-contains)))

has-no-rep : {A : 𝓤 ̇ } →  (has-decidable-equality A) → (xs : List A)
    → 𝓤 ̇ 
has-no-rep {𝓤} {A} p xs = noRep p xs ＝ xs

[]-has-no-rep : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → has-no-rep p []
[]-has-no-rep p = refl []

[a]-has-no-rep : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (a : A)
    → has-no-rep p (a :: [])
[a]-has-no-rep {𝓤} {A} p a = refl (a :: [])

::-injective : {A : 𝓤 ̇ } → (x : A) → (xs ys : List A) → (x :: xs) ＝ (x :: ys) 
    → xs ＝ ys
::-injective x xs ys x-xs-eq-x-ys = EqList-id xs ys ((pr₂ (IdListToEqList (x :: xs) (x :: ys) x-xs-eq-x-ys)))


head-of-noRep-not-in-tail : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (x : A) → (xs : List A)
    → (has-no-rep p (x :: xs)) → ¬ (contains p x xs)
head-of-noRep-not-in-tail p x xs norep-x-xs = cases-x-in-xs (dec-contains p x xs) (refl _) where

    noRep-does-not-increase-size : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (xs : List A)
        → len (noRep p xs) ≤ len xs
    noRep-does-not-increase-size p [] = *
    noRep-does-not-increase-size p (x :: xs) = cases'-x-in-xs (dec-contains p x xs) (refl _) where
        cases'-x-in-xs : (q : decidable (contains p x xs)) → (q : dec-contains p x xs ＝ q)
            → len (noRep p (x :: xs)) ≤ len (x :: xs)
        cases'-x-in-xs (yes x-in-xs) pxxs-eq-q = transport (_≤ len (x :: xs)) (a-eq-b ⁻¹) b≤c where

            a-eq-b : len (noRep p (x :: xs)) ＝ len (noRep p xs)
            a-eq-b = ap (λ t → len (if t then noRep p xs else (x :: noRep p xs))) pxxs-eq-q

            b≤c : len (noRep p xs) ≤ len (x :: xs)
            b≤c = ≤-transitive {len (noRep p xs)} {len xs} {len (x :: xs)} (noRep-does-not-increase-size p xs) (≤-succ (len xs))


        cases'-x-in-xs (no x-nin-xs) pxxs-eq-q = transport (_≤ len (x :: xs)) (a-eq-b ⁻¹) b≤c where
            a-eq-b : len (noRep p (x :: xs)) ＝ len (x :: noRep p xs)
            a-eq-b = ap (λ t → len (if t then noRep p xs else (x :: noRep p xs))) pxxs-eq-q

            b≤c : len (x :: noRep p xs) ≤ len (x :: xs)
            b≤c = noRep-does-not-increase-size p xs

    cases-x-in-xs : (q : decidable (contains p x xs)) → (q : dec-contains p x xs ＝ q) → ¬ (contains p x xs)
    cases-x-in-xs (no x-nin-xs) _ = x-nin-xs
    cases-x-in-xs (yes x-in-xs) pxxs-eq-q = !𝟘 _ ((succ-is-gt-num (len xs)) (transport (_≤ len xs) ((ap len a-eq-b) ⁻¹) (b≤c))) where
            a-eq-b : x :: xs ＝ noRep p xs
            a-eq-b =  
                x :: xs 
                    ＝⟨ norep-x-xs ⁻¹ ⟩ 
                noRep p (x :: xs) 
                    ＝⟨ ap (if_then noRep p xs else (x :: noRep p xs)) pxxs-eq-q ⟩ 
                noRep p xs 
                ∎ 
            b≤c : len (noRep p xs ) ≤ len xs
            b≤c = noRep-does-not-increase-size p xs 

tail-of-has-no-rep-has-no-rep : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (x : A) → (xs : List A)
    → (has-no-rep p (x :: xs)) → has-no-rep p xs
tail-of-has-no-rep-has-no-rep p x xs norep-x-xs = ::-injective x (noRep p xs) xs lemma where

    lemma-1 : noRep p (x :: xs) ＝ x :: (noRep p xs)
    lemma-1 = if dec-contains p x xs then noRep p xs else (x :: noRep p xs)
            ＝⟨ ap (if_then noRep p xs else (x :: noRep p xs)) (pr₂ (case-no (dec-contains p x xs) (head-of-noRep-not-in-tail p x xs norep-x-xs))) ⟩ 
        x :: noRep p xs
        ∎ 

    lemma : x :: (noRep p xs) ＝ x :: xs
    lemma = 
        x :: (noRep p xs) ＝⟨ lemma-1 ⁻¹ ⟩ 
        noRep p (x :: xs) ＝⟨ norep-x-xs ⟩ 
        x :: xs
        ∎

remove-sublist : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (a b : A) → (xs : List A)
    → contains p a (remove-first p b xs) → contains p a xs
remove-sublist p a b [] a-in-remfirst = !𝟘 _ a-in-remfirst
remove-sublist p a b (x :: xs) a-in-remfirst = cases-a-eq-x (p a x) (refl _) where
    cases-a-eq-x : (q : decidable (a ＝ x)) → (p a x ＝ q) 
        → contains p a (x :: xs)
    cases-a-eq-x (yes a-eq-x) pax-eq-q = transport (if_then 𝟙 else contains p a xs) (pax-eq-q ⁻¹) *
    cases-a-eq-x (no a-neq-x) pax-eq-q = transport id (aux-eq ⁻¹) a-in-xs where
        aux-eq : contains p a (x :: xs) ＝ contains p a xs
        aux-eq = ap (if_then 𝟙 else contains p a xs) pax-eq-q

        a-in-xs : contains p a xs
        a-in-xs = cases-b-eq-x (p b x) (refl _) where
            cases-b-eq-x : (r : decidable (b ＝ x)) → (p b x ＝ r) 
                → contains p a xs
            cases-b-eq-x (yes b-eq-x) pbx-eq-r = transport (λ t → contains p a (if t then xs else (x :: remove-first p b xs))) (pbx-eq-r) a-in-remfirst
            cases-b-eq-x (no b-neq-x) pbx-eq-r = remove-sublist p a b xs (transport (if_then 𝟙 else contains p a (remove-first p b xs)) pax-eq-q (transport (λ t → contains p a (if t then xs else (x :: remove-first p b xs))) (pbx-eq-r) a-in-remfirst))

remove-doesnt-add-rep : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (a : A) → (xs : List A)
    → (has-no-rep p xs) → has-no-rep p (remove-first p a xs)
remove-doesnt-add-rep p a [] y = y
remove-doesnt-add-rep p a (x :: xs) y = cases-a-eq-x (p a x) (refl _) where
    cases-a-eq-x : (q : decidable (a ＝ x)) → (p a x ＝ q) 
        → has-no-rep p (remove-first p a (x :: xs))
    cases-a-eq-x (yes a-eq-x) pax-eq-q = 
        transport (λ t → has-no-rep p (if t then xs else (x :: remove-first p a xs))) (pax-eq-q ⁻¹) (tail-of-has-no-rep-has-no-rep p x xs y)
    cases-a-eq-x (no a-neq-x) pax-eq-q = transport (λ t → has-no-rep p (if t then xs else (x :: remove-first p a xs))) (pax-eq-q ⁻¹)
        (noRep p (x :: remove-first p a xs) 
            ＝⟨ refl _ ⟩ 
        if dec-contains p x (remove-first p a xs) then noRep p (remove-first p a xs) else (x :: noRep p (remove-first p a xs))
            ＝⟨ ap (λ t → if t then noRep p (remove-first p a xs) else (x :: noRep p (remove-first p a xs))) (pr₂ (case-no (dec-contains p x (remove-first p a xs)) x-nin-remove)) ⟩ 
        x :: noRep p (remove-first p a xs)
            ＝⟨ ap (x ::_) (remove-doesnt-add-rep p a xs norep-xs) ⟩ 
        x :: remove-first p a xs
        ∎) where
        norep-xs : has-no-rep p xs 
        norep-xs = tail-of-has-no-rep-has-no-rep p x xs y

        x-nin-remove : ¬ (contains p x (remove-first p a xs))
        x-nin-remove ff = (head-of-noRep-not-in-tail p x xs y) (remove-sublist p x a xs ff)

remove-only-removes-single-element : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (a b : A) → (xs : List A)
    → ¬ (a ＝ b) → contains p b xs → contains p b (remove-first p a xs)
remove-only-removes-single-element p a b [] a-neq-b b-in-xs = !𝟘 _ b-in-xs
remove-only-removes-single-element p a b (x :: xs) a-neq-b b-in-xs = cases-a-eq-x (p a x) (refl _) where
    cases-a-eq-x : (q : decidable (a ＝ x)) → (p a x ＝ q) → contains p b (remove-first p a (x :: xs))
    cases-a-eq-x (yes a-eq-x) pax-eq-q = transport (λ t → contains p b (if t then xs else (x :: remove-first p a xs))) (pax-eq-q ⁻¹) (if-not-in-head-then-tail p b x xs (λ ff → a-neq-b (a-eq-x ∙ ff ⁻¹)) b-in-xs)
    cases-a-eq-x (no a-neq-x) pax-eq-q = transport (λ t → contains p b (if t then xs else (x :: remove-first p a xs))) (pax-eq-q ⁻¹) (cases-b-eq-x (p b x) (refl _)) where
        cases-b-eq-x : (r : decidable (b ＝ x)) → (p b x ＝ r) → contains p b (x :: remove-first p a xs)
        cases-b-eq-x (yes b-eq-r) pbx-eq-r = transport (if_then 𝟙 else contains p b (remove-first p a xs)) (pbx-eq-r ⁻¹) *
        cases-b-eq-x (no b-neq-r) pbx-eq-r = transport (if_then 𝟙 else contains p b (remove-first p a xs)) (pbx-eq-r ⁻¹) (remove-only-removes-single-element p a b xs a-neq-b (if-not-in-head-then-tail p b x xs b-neq-r b-in-xs))

dec-has-no-rep : {A : 𝓤 ̇ } → (p : has-decidable-equality A) → (xs : List A)
    → decidable (has-no-rep p xs)
dec-has-no-rep p [] = yes ([]-has-no-rep p)
dec-has-no-rep p (x :: xs) = cases-contains (dec-contains p x xs) (refl _) where
    cases-contains : (q : decidable (contains p x xs)) → (dec-contains p x xs ＝ q)
        → decidable (has-no-rep p (x :: xs))
    cases-contains (yes q) p-xy-eq-q = no (λ ff → (head-of-noRep-not-in-tail p x xs ff) q)
    cases-contains (no nq) p-xy-eq-q = cases-xs-rep (dec-has-no-rep p xs) (refl _) where
        cases-xs-rep : (r : decidable (has-no-rep p xs)) → (dec-has-no-rep p xs ＝ r) 
            → decidable (has-no-rep p (x :: xs))
        cases-xs-rep (yes no-rep) dec-eq-r = yes (
            noRep p (x :: xs)
                ＝⟨ ap (if_then (noRep p xs) else (x :: noRep p xs)) p-xy-eq-q ⟩ 
            x :: noRep p xs
                ＝⟨ ap (x ::_) no-rep ⟩ 
            x :: xs
            ∎)
        cases-xs-rep (no yes-rep) dec-eq-r = no (λ ff → yes-rep
            (::-injective x xs (noRep p xs) (
            x :: xs 
                ＝⟨ ff ⁻¹ ⟩ 
            noRep p (x :: xs) 
                ＝⟨ ap (if_then (noRep p xs) else (x :: noRep p xs)) p-xy-eq-q ⟩ 
            x :: noRep p xs
            ∎
            ) ⁻¹))

