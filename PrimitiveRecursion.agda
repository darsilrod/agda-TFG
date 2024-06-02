{-# OPTIONS --without-K --exact-split --auto-inline #-}
open import PropTruncations

module PrimitiveRecursion where
postulate
    pt : subsingleton-truncations-exist
open subsingleton-truncations-exist pt public

open import MLTT renaming (_+_ to _⊕_)
open import List
open import FinType
open import Arithmetic

-- 
-- 1. Definición de las funciones básicas y operaciones básicas
-- 

-- Definimos ℕ^k, con k : ℕ para definir las funciones de aridad k. Una
-- función de aridad 0 es lo mismo que una constante en ℕ, por eso definimos
-- ℕ^0 como 𝟙.
_ : {A : 𝓤 ̇ } → A ≃ (𝟙 → A) 
_ = 𝟙-recursion _ , ((λ z → z *) , (λ x → funext (λ y → refl (𝟙-recursion _ (x *) y)))) , ((λ z → z *) , refl)

ℕ^ : (k : ℕ) → 𝓤₀ ̇ 
ℕ^  0              = 𝟙
ℕ^  1              = ℕ
ℕ^ (succ (succ k)) = ℕ × (ℕ^ (succ k))

-- También podríamos haber usado listas de exactamente n elementos, i.e.
-- vectores, pero estos dos tipos son equivalentes.
n-tuple-to-vect-n : {n : ℕ} → ℕ^ n → Vect ℕ n 
n-tuple-to-vect-n {0}              *       = nil
n-tuple-to-vect-n {1}              x       = x ++ nil
n-tuple-to-vect-n {succ (succ n)} (x , xs) = x ++ (n-tuple-to-vect-n xs)

vect-n-to-n-tuple : {n : ℕ} → Vect ℕ n → ℕ^ n 
vect-n-to-n-tuple {0}              nil       = *
vect-n-to-n-tuple {1}             (x ++ nil) = x
vect-n-to-n-tuple {succ (succ n)} (x ++ v)   = x , vect-n-to-n-tuple v

vect-n-to-n-tuple-has-inverse : (n : ℕ) → has-inverse (vect-n-to-n-tuple {n})
vect-n-to-n-tuple-has-inverse n = (n-tuple-to-vect-n {n}) , (lemma-1 n , lemma-2 n) where
    lemma-1 : (n : ℕ) → (xs : ℕ^ n) → vect-n-to-n-tuple (n-tuple-to-vect-n xs) ＝ xs
    lemma-1  0               *       = refl _
    lemma-1  1               x       = refl _
    lemma-1 (succ (succ n)) (x , xs) = ap (x ,_ ) (lemma-1 (succ n) xs) 

    lemma-2 : (n : ℕ) → (v : Vect ℕ n) → n-tuple-to-vect-n (vect-n-to-n-tuple v) ＝ v
    lemma-2  0               nil       = refl nil
    lemma-2 (succ zero)     (x ++ nil) = refl (x ++ nil)
    lemma-2 (succ (succ n)) (x ++ v)   = ap (x ++_) (lemma-2 (succ n) v)

Vect-n-equiv-ℕ^k : (n : ℕ) → Vect ℕ n ≃ ℕ^ n
Vect-n-equiv-ℕ^k n = vect-n-to-n-tuple , has-inverse-is-equivalence vect-n-to-n-tuple (vect-n-to-n-tuple-has-inverse n)

-- Ejemplo:
ℕ^2 : 𝓤₀ ̇ 
ℕ^2 = ℕ^ 2 

-- 1.1. Función básica: la función sucesor succ : ℕ → ℕ

_ : (x : ℕ) → succ x ＝ x + 1
_ = λ x → refl (succ x) 


-- 1.2. Función básica: Función cte. 0 de aridad n
zero-fun : (n : ℕ) → ℕ^ n → ℕ
zero-fun _ _ = 0

-- Definimos las proyecciones de aridad n sobre la k-ésima coordenada. Para que
-- tenga sentido, la coordenada k ha de estar entre 1 y n, y usamos el tipo Fin
-- para imponer esta condición a nivel de tipos.

π' : (n : ℕ) → ℕ^ n → Fin n → ℕ
π'  0               _       ff      = !𝟘 _ ff
π'  1               x       _       = x
π' (succ (succ _)) (x , _) (inr _)  = x
π' (succ (succ n)) (_ , xs) (inl i) = π' (succ n) xs i

-- 1.3. Función básica: proyección de aridad n sobre la k-ésima coordenada
π : (n : ℕ) → (k : ℕ) → {1 ≤ k} → {k ≤ n}
    → ℕ^ n → ℕ
π n k {q} {r} xs = π' n xs (!Fin k q r)

-- Ejemplos:
π₁ : ℕ^2 → ℕ
π₁ xs = π 2 1 xs

_ : (x y : ℕ) → π₁ (x , y) ＝ x 
_ = λ x y → refl x

π₂ : ℕ^2 → ℕ
π₂ xs = π 2 2 xs

_ : (x y : ℕ) → π₂ (x , y) ＝ y 
_ = λ x y → refl y

-- 1.4. Operación básica: Composición 
-- Dada h : ℕ^ k → ℕ y g₁, ..., gₖ : ℕ^ n → ℕ, podemos construir la función
-- f : ℕ^ n → ℕ dada por 
-- f(x₁, ..., xₙ) = h(g₁(x₁, ..., xₙ), ..., gₙ(x₁, ..., xₙ)).
apply-vect : {k n : ℕ} → Vect (ℕ^ n → ℕ) k → ℕ^ n → ℕ^ k 
apply-vect {0}              _         _  = *
apply-vect {1}             (g ++ nil) xs = g xs
apply-vect {succ (succ k)} (g ++ gs)  xs = (g xs) , (apply-vect gs xs)

PR-comp : {k n : ℕ}
    → (h : ℕ^ k → ℕ) → Vect (ℕ^ n → ℕ) k
    → ℕ^ n
    → ℕ
PR-comp h gs xs = h (apply-vect gs xs)

-- 1.5. Operación básica: Recursión 
-- Dadas g : ℕ^ k → ℕ y h : ℕ^ (k + 2) → ℕ, podemos definir una fución 
-- f : ℕ^ (k + 1) → ℕ dada por 
-- f(0,     x₁, ..., xₖ) = g(x₁, ..., xₖ)
-- f(x + 1, x₁, ..., xₖ) = h(x, f(x, x₁, ..., xₖ), x₁, ..., xₖ).

-- Es necesaria una función auxiliar, porque la función trabaja por inducción
-- en la primera variable de ℕ^k, pero como este tipo no está definido como
-- tipo inductivo, Agda no puede garantizar que la función siempre termine.
ρ-operator' : {k : ℕ} → (g : ℕ^ k → ℕ) → (h : ℕ^ (k + 2) → ℕ)
    → (xs : ℕ^ (k + 1)) → (n : ℕ) → (p : (π (k + 1) 1 xs) ＝ n) → ℕ
ρ-operator' {0}      g _  0               0       (refl _) = g *
ρ-operator' {0}      g h (succ n)        (succ n) (refl _) = h (n , (ρ-operator' g h n n (refl _)))
ρ-operator' {succ k} g _ (0 , xs)         0       (refl _) = g xs
ρ-operator' {succ k} g h ((succ n) , xs) (succ n) (refl _) = h (n , ρ-operator' g h (n , xs) n (refl _) , xs)

ρ-operator : {k : ℕ} → (g : ℕ^ k → ℕ) → (h : ℕ^ (k + 2) → ℕ)
    → ℕ^ (k + 1) → ℕ
ρ-operator {k} g h xs = ρ-operator' g h xs (π (k + 1) 1 xs) (refl _)

-- Función auxiliar que será necesaria.

map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {n : ℕ} → Vect A n → (A → B) → Vect B n 
map {n = 0}       nil     f = nil
map {n = succ n} (x ++ v) f = f x ++ map v f

-- 
-- 2. El tipo de las funciones primitivas recursiva
-- 

data 𝓟𝓡ⁿ : (n : ℕ) → (ℕ^ n → ℕ) → 𝓤₀ ̇  where
    -- La función sucesor es primitiva recursiva.
    succ-PR : 𝓟𝓡ⁿ 1 succ 

    -- La función constantemente cero de aridad n es primitiva recursiva.
    zero-PR : (n : ℕ) → 𝓟𝓡ⁿ n (zero-fun n)

    -- Las k proyecciones de aridad n son primitivas recursivas.
    proy-PR : (n : ℕ) → (k : ℕ) → {q : 1 ≤ k} → {r : k ≤ n} 
        → 𝓟𝓡ⁿ n (π n k {q} {r})
        
    -- La composición de funciones primitivas recursivas es primitiva recursiva.
    𝓒-PR : {n k : ℕ} → {h : ℕ^ k → ℕ} 
        → 𝓟𝓡ⁿ k h
        → (gspair : Vect (Σ g ꞉ (ℕ^ n → ℕ) , 𝓟𝓡ⁿ n g) k) 
        → 𝓟𝓡ⁿ n (PR-comp h (map gspair pr₁))

    -- La recursión de funciones primitivas recursivas es primitiva recursiva.
    ρ-PR : {n : ℕ} → {g : ℕ^ n → ℕ} → {h : (ℕ^ (n + 2)) → ℕ}
        → 𝓟𝓡ⁿ n g → 𝓟𝓡ⁿ (n + 2) h 
        → 𝓟𝓡ⁿ (n + 1) (ρ-operator g h)

-- Recursión para el tipo de las funciones primitivas recursivas.
𝓟𝓡-recursion : {P : (n : ℕ) → (f : ℕ^ n → ℕ) → (𝓟𝓡ⁿ n f) → 𝓤 ̇ }
    → P 1 succ succ-PR 
    → ((n : ℕ) → P n (zero-fun n) (zero-PR n))
    → ((n : ℕ) → (k : ℕ) → {q : 1 ≤ k} → {r : k ≤ n} → P n (π n k {q} {r}) (proy-PR n k {q} {r}))
    → ({n k : ℕ} → {h : ℕ^ k → ℕ} 
        → (hpr : 𝓟𝓡ⁿ k h)
        → (gspair : Vect (Σ g ꞉ (ℕ^ n → ℕ) , 𝓟𝓡ⁿ n g) k) 
        → P n (PR-comp h (map gspair pr₁)) (𝓒-PR hpr gspair))
    → ({n : ℕ} → {g : ℕ^ n → ℕ} → {h : (ℕ^ (n + 2)) → ℕ}
        → (gpr : 𝓟𝓡ⁿ n g) → (hpr : 𝓟𝓡ⁿ (n + 2) h) 
        → P (n + 1) (ρ-operator g h) (ρ-PR gpr hpr))
    → (n : ℕ) → (f : ℕ^ n → ℕ) → (fpr : 𝓟𝓡ⁿ n f) → P n f fpr
𝓟𝓡-recursion p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec .1       .succ              succ-PR                                    = p-succ
𝓟𝓡-recursion p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n        .(zero-fun n)     (zero-PR .n)                                = p-n-zero n
𝓟𝓡-recursion p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n        .(π n k)          (proy-PR .n k)                              = p-n-k-π n k
𝓟𝓡-recursion p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n        .(PR-comp h       (map gspair pr₁)) (𝓒-PR {h = h} hpr gspair) = hpr-gspair-comp hpr gspair
𝓟𝓡-recursion p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec .(_ + 1) .(ρ-operator _ _) (ρ-PR gpr hpr)                              = gpr-hpr-rec gpr hpr

-- 2.1. Teorema: si una propiedad P se cumple para las funciones básicas y es
-- cerrada por composición y recursión de funciones, entonces P se cumple para 
-- toda función recursiva recursiva.

interleaved mutual 
    𝓟𝓡-induction : {P : (n : ℕ) → (f : ℕ^ n → ℕ) → 𝓤 ̇ }
        → P 1 succ
        → ((n : ℕ) → P n (zero-fun n))
        → ((n : ℕ) → (k : ℕ) → {q : 1 ≤ k} → {r : k ≤ n} → P n (π n k {q} {r}))
        → ({n k : ℕ} → {h : ℕ^ k → ℕ} 
            → (hpr : P k h)
            → (gspair : Vect (Σ g ꞉ (ℕ^ n → ℕ) , P n g) k) 
            → P n (PR-comp h (map gspair pr₁)))
        → ({n : ℕ} → {g : ℕ^ n → ℕ} → {h : (ℕ^ (n + 2)) → ℕ}
            → (gpr : P n g) → (hpr : P (n + 2) h) 
            → P (n + 1) (ρ-operator g h))
        → (n : ℕ) → (f : ℕ^ n → ℕ) → (fpr : 𝓟𝓡ⁿ n f) → P n f

    𝓟𝓡-induction' : {P : (n : ℕ) → (f : ℕ^ n → ℕ) → 𝓤 ̇ }
        → P 1 succ
        → ((n : ℕ) → P n (zero-fun n))
        → ((n : ℕ) → (k : ℕ) → {q : 1 ≤ k} → {r : k ≤ n} → P n (π n k {q} {r}))
        → ({n k : ℕ} → {h : ℕ^ k → ℕ} 
            → (hpr : P k h)
            → (gspair : Vect (Σ g ꞉ (ℕ^ n → ℕ) , P n g) k) 
            → P n (PR-comp h (map gspair pr₁)))
        → ({n : ℕ} → {g : ℕ^ n → ℕ} → {h : (ℕ^ (n + 2)) → ℕ}
            → (gpr : P n g) → (hpr : P (n + 2) h) 
            → P (n + 1) (ρ-operator g h))
        → (n : ℕ) → {k : ℕ} → (gspair : Vect (Σ g ꞉ (ℕ^ n → ℕ) , 𝓟𝓡ⁿ n g) k)
        → Σ v ꞉ (Vect (Σ g ꞉ (ℕ^ n → ℕ) , P n g) k) , (map gspair pr₁ ＝ map v pr₁)
    
    𝓟𝓡-induction         p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec .1 .succ                         succ-PR                   = p-succ
    𝓟𝓡-induction         p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n .(zero-fun n)                 (zero-PR .n)               = p-n-zero n
    𝓟𝓡-induction         p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n .(π n k)                      (proy-PR .n k)             = p-n-k-π n k
    𝓟𝓡-induction {P = P} p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n .(PR-comp h (map gspair pr₁)) (𝓒-PR {h = h} pr-h gspair) = 
        transport 
        (λ v → P n (PR-comp h v)) 
        (pr₂ v,p ⁻¹) 
        (hpr-gspair-comp (𝓟𝓡-induction p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec _ _ pr-h) (pr₁ v,p))
        where
        v,p = 𝓟𝓡-induction' p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec _ gspair

    𝓟𝓡-induction p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec .(_ + 1) .(ρ-operator _ _) (ρ-PR pr-g pr-h) = gpr-hpr-rec 
        (𝓟𝓡-induction p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec _ _ pr-g) 
        (𝓟𝓡-induction p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec _ _ pr-h)

    𝓟𝓡-induction' p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n   nil             = nil , (refl nil)
    𝓟𝓡-induction' p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n ((g , pr-g) ++ v) = (g , (𝓟𝓡-induction p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n g pr-g) ++ pr₁ v,p) 
        , ap (g ++_) (pr₂ v,p) where
        v,p = 𝓟𝓡-induction' p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n v

-- Podemos omitir la aridad, porque se infiere del argumento.
𝓟𝓡 : {n : ℕ} → (ℕ^ n → ℕ) → 𝓤₀ ̇  
𝓟𝓡 {n} f = 𝓟𝓡ⁿ n f 

-- 2.3. Funciones meramente primitivas recursivas
-- Como proposición, obtenemos el tipo de funciones meramente primitivas
-- recursivas.
𝓟𝓡ⁿ-prop : (n : ℕ) → (ℕ^ n → ℕ) → 𝓤₀ ̇ 
𝓟𝓡ⁿ-prop n f = ∥ 𝓟𝓡ⁿ n f ∥

-- Recursión para funciones meramente primitivas recursivas.
𝓟𝓡-prop-recursion : {P : (n : ℕ) → (f : ℕ^ n → ℕ) → (𝓟𝓡ⁿ-prop n f) → 𝓤 ̇ }
    → ((n : ℕ) → (f : ℕ^ n → ℕ) → (fpr : 𝓟𝓡ⁿ-prop n f) → is-subsingleton (P n f fpr))
    → P 1 succ ∣ succ-PR ∣ 
    → ((n : ℕ) → P n (zero-fun n) ∣ zero-PR n ∣)
    → ((n : ℕ) → (k : ℕ) → {q : 1 ≤ k} → {r : k ≤ n} → P n (π n k {q} {r}) ∣ proy-PR n k {q} {r} ∣)
    → ({n k : ℕ} → {h : ℕ^ k → ℕ} 
        → (hpr : 𝓟𝓡ⁿ k h)
        → (gspair : Vect (Σ g ꞉ (ℕ^ n → ℕ) , 𝓟𝓡ⁿ n g) k) 
        → P n (PR-comp h (map gspair pr₁)) ∣ 𝓒-PR hpr gspair ∣)
    → ({n : ℕ} → {g : ℕ^ n → ℕ} → {h : (ℕ^ (n + 2)) → ℕ}
        → (gpr : 𝓟𝓡ⁿ n g) → (hpr : 𝓟𝓡ⁿ (n + 2) h) 
        → P (n + 1) (ρ-operator g h) ∣ ρ-PR gpr hpr ∣ )
    → (n : ℕ) → (f : ℕ^ n → ℕ) → (fpr : 𝓟𝓡ⁿ-prop n f) → P n f fpr
𝓟𝓡-prop-recursion {𝓤} {P = P} p-sub p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n f fpr = ∥∥-recursion 
    (p-sub n f fpr) 
    (λ fpr-constr → 
        transport (λ x → P n f x) 
        (∥∥-is-subsingleton ∣ fpr-constr ∣ fpr) 
        (𝓟𝓡-recursion {P = Q} p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n f fpr-constr)) 
    fpr where
        
        Q : (n : ℕ) → (f : ℕ^ n → ℕ) → (𝓟𝓡ⁿ n f) → 𝓤 ̇ 
        Q n f fpr-constr = P n f ∣ fpr-constr ∣

-- 2.4. Teorema: si una proposición P se cumple para las funciones básicas y es
-- cerrada por composición y recursión de funciones, 
-- entonces P se cumple para toda función meramente primitiva recursiva.
𝓟𝓡-prop-induction : {P : (n : ℕ) → (f : ℕ^ n → ℕ) → 𝓤 ̇ }
    → ((n : ℕ) → (f : ℕ^ n → ℕ) → is-subsingleton (P n f))
    → P 1 succ
    → ((n : ℕ) → P n (zero-fun n))
    → ((n : ℕ) → (k : ℕ) → {q : 1 ≤ k} → {r : k ≤ n} → P n (π n k {q} {r}))
    → ({n k : ℕ} → {h : ℕ^ k → ℕ} 
        → (hpr : P k h)
        → (gspair : Vect (Σ g ꞉ (ℕ^ n → ℕ) , P n g) k) 
        → P n (PR-comp h (map gspair pr₁)))
    → ({n : ℕ} → {g : ℕ^ n → ℕ} → {h : (ℕ^ (n + 2)) → ℕ}
        → (gpr : P n g) → (hpr : P (n + 2) h) 
        → P (n + 1) (ρ-operator g h))
    → (n : ℕ) → (f : ℕ^ n → ℕ) → (fpr : 𝓟𝓡ⁿ-prop n f) → P n f
𝓟𝓡-prop-induction p-n-f-prop p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n f f-pr = ∥∥-recursion (p-n-f-prop n f) (𝓟𝓡-induction p-succ p-n-zero p-n-k-π hpr-gspair-comp gpr-hpr-rec n f) f-pr

-- Podemos omitir la aridad.
𝓟𝓡-prop : {n : ℕ} → (ℕ^ n → ℕ) → 𝓤₀ ̇ 
𝓟𝓡-prop {n} = 𝓟𝓡ⁿ-prop n

--
-- 3. Ejemplos de funciones primitivas recursivas y algunas propiedades
--

succ-is-𝓟𝓡̂-prop : 𝓟𝓡-prop succ
succ-is-𝓟𝓡̂-prop = ∣ succ-PR ∣

zero-fun-n-is-𝓟𝓡-prop : (n : ℕ) → 𝓟𝓡-prop (zero-fun n) 
zero-fun-n-is-𝓟𝓡-prop n = ∣ (zero-PR n) ∣

π-n-k-is-𝓟𝓡-prop : (n : ℕ) → (k : ℕ) → {p : 1 ≤ k} → {q : k ≤ n} → 𝓟𝓡-prop (π n k {p} {q})
π-n-k-is-𝓟𝓡-prop n k {p} {q} = ∣ proy-PR n k {p} {q} ∣

id-is-𝓟𝓡-prop : 𝓟𝓡-prop (𝑖𝑑 ℕ)
id-is-𝓟𝓡-prop = ∣ (proy-PR 1 1) ∣

kth-arity-const : (k : ℕ) → ℕ 
    → ℕ^ k → ℕ 
kth-arity-const _ x = λ _ → x

PR-comp-is-𝓟𝓡-prop : {n k : ℕ} → {h : ℕ^ k → ℕ} 
    → 𝓟𝓡-prop h
    → (gspair : Vect (Σ g ꞉ (ℕ^ n → ℕ) , 𝓟𝓡-prop g) k) 
    → 𝓟𝓡-prop (PR-comp h (map gspair pr₁))
PR-comp-is-𝓟𝓡-prop hpr gspr = ∥∥-recursion ∥∥-is-subsingleton (λ hpr-const → ∥∥-recursion ∥∥-is-subsingleton (λ gspr-const → ∣ lemma hpr-const gspr gspr-const ∣) (vect-∥∥-to-∥vect∥ gspr)) hpr where

    lemma : {n k : ℕ} → {h : ℕ^ k → ℕ} → 𝓟𝓡 h
        → (gspr : Vect (Σ g ꞉ (ℕ^ n → ℕ) , 𝓟𝓡-prop g) k) 
        → Σ v' ꞉ (Vect (Σ g ꞉ (ℕ^ n → ℕ) , (𝓟𝓡 g)) k) , (map gspr pr₁ ＝ map v' pr₁)
        → 𝓟𝓡 (PR-comp h (map gspr pr₁))
    lemma {h = h} hpr-const gspr v' = transport (λ x → 𝓟𝓡 (PR-comp h x)) (pr₂ v' ⁻¹) (𝓒-PR hpr-const (pr₁ v')) 
    
    vect-∥∥-to-∥vect∥ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } → {Y : X → 𝓥 ̇ } {n : ℕ} 
        → (v : Vect (Σ x ꞉ X , ∥ Y x ∥ ) n)
        → ∥ Σ v' ꞉ (Vect (Σ x ꞉ X , Y x ) n) , (map v pr₁ ＝ map v' pr₁) ∥
    vect-∥∥-to-∥vect∥  nil      = ∣ (nil , refl nil) ∣
    vect-∥∥-to-∥vect∥ (p ++ ps) = ∥∥-recursion ∥∥-is-subsingleton (λ ps-lift → ∥∥-recursion ∥∥-is-subsingleton (λ lift-p → ∣ ((((pr₁ p) , lift-p) ++ pr₁ ps-lift) , ap (pr₁ p ++_) (pr₂ ps-lift)) ∣) (pr₂ p)) (vect-∥∥-to-∥vect∥ ps)

PR-rec-is-𝓟𝓡-prop : {n : ℕ} → {g : ℕ^ n → ℕ} → {h : (ℕ^ (n + 2)) → ℕ}
        → (gpr : 𝓟𝓡-prop g) → (hpr : 𝓟𝓡-prop h) 
        → 𝓟𝓡-prop (ρ-operator g h)
PR-rec-is-𝓟𝓡-prop gpr hpr = ∥∥-recursion ∥∥-is-subsingleton (λ gpr-const → ∥∥-recursion ∥∥-is-subsingleton (λ hpr-const → ∣ ρ-PR gpr-const hpr-const ∣) hpr ) gpr

comp-is-𝓟𝓡 : (f g : ℕ → ℕ) → 𝓟𝓡 f → 𝓟𝓡 g
    → 𝓟𝓡 (g ∘ f)
comp-is-𝓟𝓡 f g prf prg = 𝓒-PR prg ((f , prf) ++ nil) 


comp-is-𝓟𝓡-prop : (f g : ℕ → ℕ) → 𝓟𝓡-prop f → 𝓟𝓡-prop g
    → 𝓟𝓡-prop (g ∘ f)
comp-is-𝓟𝓡-prop f g fpr gpr = PR-comp-is-𝓟𝓡-prop gpr ((f , fpr) ++ nil)

-- 

kth-arity-const-is-𝓟𝓡 : (k : ℕ) (x : ℕ) → 𝓟𝓡 (kth-arity-const k x)
kth-arity-const-is-𝓟𝓡 k  0       = zero-PR k
kth-arity-const-is-𝓟𝓡 k (succ x) = 𝓒-PR succ-PR ((kth-arity-const k x , kth-arity-const-is-𝓟𝓡 k x) ++ nil)

kth-arity-const-is-𝓟𝓡-prop : (k : ℕ) (x : ℕ) → 𝓟𝓡-prop (kth-arity-const k x)
kth-arity-const-is-𝓟𝓡-prop k x = ∣ kth-arity-const-is-𝓟𝓡 k x ∣

--

uncurry-addition : ℕ^2 → ℕ 
uncurry-addition (x , y) = x + y 

addition' : ℕ^2 → ℕ 
addition' = ρ-operator (π 1 1) (PR-comp succ ((π 3 2) ++ nil))

addition'-is-𝓟𝓡 : 𝓟𝓡 addition'
addition'-is-𝓟𝓡 = ρ-PR (proy-PR 1 1) (𝓒-PR succ-PR (((π 3 2) , (proy-PR 3 2)) ++ nil))

addition'-is-𝓟𝓡-prop : 𝓟𝓡-prop addition'
addition'-is-𝓟𝓡-prop = ∣ addition'-is-𝓟𝓡 ∣ 

addition'-is-addition : (x y : ℕ) → addition' (x , y) ＝ uncurry-addition (x , y)
addition'-is-addition 0 y = 
    addition' (0 , y)        ＝⟨ refl _ ⟩ 
    y                        ＝⟨ (Peano.zero+n y) ⁻¹ ⟩ 
    0 + y                    ＝⟨ refl _ ⟩ 
    uncurry-addition (0 , y) ∎
addition'-is-addition (succ x) y = 
    addition' (succ x , y)   ＝⟨ refl _ ⟩ 
    succ (addition' (x , y)) ＝⟨ ap succ (addition'-is-addition x y) ⟩ 
    succ (x + y)             ＝⟨ (Peano.succ+y x y) ⁻¹ ⟩ 
    succ x + y               ＝⟨ refl _ ⟩ 
    uncurry-addition (succ x , y)
    ∎

addition'-sim-addition : addition' ∼ uncurry-addition 
addition'-sim-addition (x , y) = addition'-is-addition x y

uncurry-addition-is-𝓟𝓡 : 𝓟𝓡 uncurry-addition 
uncurry-addition-is-𝓟𝓡 = transport 𝓟𝓡 (funext addition'-sim-addition) addition'-is-𝓟𝓡

uncurry-addition-is-𝓟𝓡-prop : 𝓟𝓡-prop uncurry-addition 
uncurry-addition-is-𝓟𝓡-prop = ∣ uncurry-addition-is-𝓟𝓡 ∣ 

-- 

uncurry-multiplication :  ℕ^2 → ℕ 
uncurry-multiplication (x , y) = x ⋆ y 

multiplication' : ℕ^2 → ℕ 
multiplication' = ρ-operator (kth-arity-const 1 0) (PR-comp addition' ((π 3 2) ++ (π 3 3) ++ nil))


multiplication'-is-𝓟𝓡 : 𝓟𝓡 multiplication'
multiplication'-is-𝓟𝓡 = ρ-PR (zero-PR 1) (𝓒-PR addition'-is-𝓟𝓡 (((π 3 2) , (proy-PR 3 2)) ++ ((π 3 3) , (proy-PR 3 3) ++ nil)))

multiplication'-is-𝓟𝓡-prop : 𝓟𝓡-prop multiplication'
multiplication'-is-𝓟𝓡-prop = ∣ multiplication'-is-𝓟𝓡 ∣

multiplication'-is-multiplication : (x y : ℕ) → multiplication' (x , y) ＝ uncurry-multiplication (x , y)
multiplication'-is-multiplication  0       y = 
    multiplication' (0 , y)  ＝⟨ refl _ ⟩ 
    0                        ＝⟨ (Peano.zero*n y) ⁻¹ ⟩ 
    0 ⋆ y                    ＝⟨ refl _ ⟩ 
    uncurry-multiplication (0 , y) ∎
multiplication'-is-multiplication (succ x) y = 
    multiplication' (succ x , y)            ＝⟨ refl _ ⟩ 
    addition' (multiplication' (x , y) , y) ＝⟨ addition'-is-addition (multiplication' (x , y)) y ⟩ 
    multiplication' (x , y) + y             ＝⟨ ap (_+ y) (multiplication'-is-multiplication x y) ⟩ 
    x ⋆ y + y                               ＝⟨ (Peano.succ*y x y) ⁻¹ ⟩ 
    succ x ⋆ y                              ＝⟨ refl _ ⟩ 
    uncurry-multiplication (succ x , y)
    ∎

multiplication'-sim-multiplication : multiplication' ∼ uncurry-multiplication 
multiplication'-sim-multiplication (x , y) = multiplication'-is-multiplication x y

uncurry-multiplication-is-𝓟𝓡 : 𝓟𝓡 uncurry-multiplication 
uncurry-multiplication-is-𝓟𝓡 = transport 𝓟𝓡 (funext multiplication'-sim-multiplication) multiplication'-is-𝓟𝓡

uncurry-multiplication-is-𝓟𝓡-prop : 𝓟𝓡-prop uncurry-multiplication 
uncurry-multiplication-is-𝓟𝓡-prop = ∣ uncurry-multiplication-is-𝓟𝓡 ∣ 

-- 

pred : ℕ → ℕ 
pred  0       = 0 
pred (succ n) = n

pred' : ℕ → ℕ
pred' = ρ-operator (zero-fun 0) (π 2 1)

pred'-is-pred : (n : ℕ) → pred' n ＝ pred n 
pred'-is-pred  0       = refl 0
pred'-is-pred (succ n) = refl n

pred'-is-𝓟𝓡 : 𝓟𝓡 pred'
pred'-is-𝓟𝓡 = ρ-PR (zero-PR 0) (proy-PR 2 1)

pred'-is-𝓟𝓡-prop : 𝓟𝓡-prop pred'
pred'-is-𝓟𝓡-prop = ∣ pred'-is-𝓟𝓡 ∣ 

pred-is-𝓟𝓡 : 𝓟𝓡 pred
pred-is-𝓟𝓡 = transport 𝓟𝓡 (funext pred'-is-pred) pred'-is-𝓟𝓡

pred-is-𝓟𝓡-prop : 𝓟𝓡-prop pred
pred-is-𝓟𝓡-prop = ∣ pred-is-𝓟𝓡 ∣ 

--

sg : ℕ → ℕ 
sg  0       = 0
sg (succ _) = 1

sg' : ℕ → ℕ 
sg' = ρ-operator (zero-fun 0) (kth-arity-const 2 1)

sg'-is-sg : (n : ℕ) → sg' n ＝ sg n 
sg'-is-sg  0       = refl 0
sg'-is-sg (succ n) = refl 1

sg'-is-𝓟𝓡 : 𝓟𝓡 sg' 
sg'-is-𝓟𝓡 = ρ-PR (zero-PR 0) (kth-arity-const-is-𝓟𝓡 2 1)

sg-is-𝓟𝓡 : 𝓟𝓡 sg 
sg-is-𝓟𝓡 = transport 𝓟𝓡 (funext sg'-is-sg) sg'-is-𝓟𝓡

sg-is-𝓟𝓡-prop : 𝓟𝓡-prop sg 
sg-is-𝓟𝓡-prop = ∣ sg-is-𝓟𝓡 ∣ 
