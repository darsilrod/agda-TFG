{-# OPTIONS --without-K --exact-split --auto-inline #-}
open import PropTruncations

module LOOP where

-- open subsingleton-truncations-exist pt public

open import MLTT renaming (_+_ to _⊕_)
open import Arithmetic 
open import List
open import PrimitiveRecursion
open import FinType
open import Decidability

--
-- 1. El lenguaje LOOP
--

-- 1.1. El lenguaje LOOP usa variables del tipo X n, con n : ℕ.
data VAR : 𝓤₀ ̇  where
    X : ℕ → VAR

-- La variable X₀ representará la salida del programa.
X₀ : VAR
X₀ = X 0

-- 1.2. El lenguaje LOOP tiene tres tipos de instrucciones.
data LOOP-Instr : 𝓤₀ ̇  where
    CLEAR    : VAR → LOOP-Instr
    INC      : VAR → LOOP-Instr 
    LOOP_DO_ : VAR → List LOOP-Instr → LOOP-Instr

-- 1.3. Un LOOP-programa es una secuencia de instrucciones.
-- De esta manera, cualquier sucesión de instrucciones que sea sintácticamente
-- correcta es un LOOP-programa bien formado.
LOOP-program = List LOOP-Instr

END : List LOOP-Instr
END = []

-- Podemos hablar de las instrucciones desde cierto punto del programa.
program-from : ℕ → LOOP-program → LOOP-program 
program-from  0                    p  = []
program-from  1                    [] = []
program-from  1              (x :: p) = p
program-from (succ (succ n))       [] = []
program-from (succ (succ n)) (x :: p) = program-from (succ n) p


-- Ejemplo 1. 
-- El programa vacío es un LOOP-programa.
empty-program : LOOP-program
empty-program = END 

-- Ejemplo 2. Un LOOP-programa con varias instrucciones.
_ : LOOP-program
_  = 
    INC (X 1)       :: 
    INC (X 1)       :: 
    END  

-- Ejemplo 3. Un LOOP-programa con bucles.
eg-LOOP : LOOP-program
eg-LOOP = 
    LOOP (X 1) DO (
        INC X₀      :: 
    END)            :: 
    LOOP (X 2) DO (
        INC X₀      :: 
    END)            :: 
    END 

--
-- 2. Interpretación de los LOOP-programas
--

-- 2.1. Un estado de un LOOP-programa es una lista de manera que el valor en la
-- posición n-ésima representa el valor que toma la variable X n.

STATE = List ℕ

-- Ejemplo de estado: X₀ = 3, X₁ = 1, X₂ = 5
eg-σ : STATE
eg-σ = 3 :: 1 :: 5 :: []

-- 2.2. El valor de la variable X n se puede recuperar. Si en la posición 
-- n-ésima no hay ningún valor, se entiende que la variable toma el valor 0.
value-at : STATE → VAR → ℕ 
value-at []         _           = 0 
value-at (x :: _)  (X 0)        = x
value-at (_ :: xs) (X (succ n)) = value-at xs (X n)

-- Ejemplos: 
_ : value-at eg-σ (X 2) ＝ 5 
_ = refl _

_ : value-at eg-σ (X 7) ＝ 0 
_ = refl _ 

-- 2.3. Operaciones con estados

-- 2.3.1. Borrar el valor de una variable en un estado.
clear-value : STATE → VAR → STATE 
clear-value []         x           = []
clear-value (y₀ :: σ) (X zero)     = 0 :: σ
clear-value (y₀ :: σ) (X (succ n)) = y₀ :: clear-value σ (X n)

_ : clear-value eg-σ (X 2) ＝ (3 :: 1 :: 0 :: [])
_ = refl _

-- 2.3.2. Incrementar el valor de una variable en un estado.
inc-value : STATE → VAR → STATE 
inc-value []        (X 0)        = 1 :: []
inc-value (y₀ :: σ) (X 0)        = (y₀ + 1) :: σ
inc-value []        (X (succ n)) = 0 :: (inc-value [] (X n))
inc-value (y₀ :: σ) (X (succ n)) = y₀ :: (inc-value σ (X n))

_ : inc-value eg-σ (X 2) ＝ (3 :: 1 :: 6 :: [])
_ = refl _

_ : inc-value eg-σ (X 4) ＝ (3 :: 1 :: 5 :: 0 :: 1 :: [])
_ = refl _


-- 2.4. El estado inicial de una tupla (x₁, ..., xₙ) es el que pone en las 
-- variables los valores X₀ = 0, X 1 = x₁, ..., X n = xₙ.
INIT-STATE' : {n : ℕ} → ℕ^ n → STATE
INIT-STATE' {0}             _        = []
INIT-STATE' {1}             x        = x :: []
INIT-STATE' {succ (succ n)} (x , xs) = x :: INIT-STATE' xs

INIT-STATE : {n : ℕ} → ℕ^ n → STATE
INIT-STATE xs = 0 :: INIT-STATE' xs

init-state'-has-len-n : {n : ℕ} → (xs : ℕ^ n) → len (INIT-STATE' xs) ＝ n 
init-state'-has-len-n {0}              _       = refl 0
init-state'-has-len-n {1}              x       = refl 1
init-state'-has-len-n {succ (succ n)} (x , xs) = ap succ (init-state'-has-len-n xs)
 
-- 2.5. Dado una tupla inicial y un programa, podemos hablar del estado
-- resultante de la ejecución del programa.

interleaved mutual
    loop-n-times : ℕ → STATE → LOOP-program → STATE
    execution-from-state : STATE → LOOP-program → STATE
    
    -- Interpretación de las intrucciones de un LOOP-programa:

    -- Ejecutar un programa vacío no cambia el estado de las variables.
    execution-from-state σ₀ []                    = σ₀
    
    -- Ejecutar la instrucción CLEAR x borra el valor de la variable x en el
    -- estado σ₀.
    execution-from-state σ₀ (CLEAR x :: p)        = execution-from-state (clear-value σ₀ x) p

    -- Ejecutar la instrucción INC x aumenta en uno el valor de la variable x 
    -- en el estado σ₀.
    execution-from-state σ₀ (INC x :: p)          = execution-from-state (inc-value σ₀ x) p

    -- Ejecutar la instrucción LOOP x do p' ejecuta el subprograma p' y veces,
    -- donde y es el valor que toma la variable x, y siendo la ejecución
    -- inicial de p a partir del estado σ₀, y las sucesivas iteraciones con los
    -- estados obtenidos de las iteraciones anteriores.
    execution-from-state σ₀ ((LOOP x DO p') :: p) = execution-from-state (loop-n-times (value-at σ₀ x) σ₀ p') p

    loop-n-times 0 σ₀ p = σ₀
    loop-n-times (succ n) σ₀ p = loop-n-times n (execution-from-state σ₀ p) p

-- 2.6. La función de aridad n calculada por un LOOP-programa p es la función
-- que a cada tupla xs : ℕ^ n le asocia el valor final de la variable X₀ al
-- ejecutarse p desde el estado inicial de xs.
⟦_⟧^ : LOOP-program → (n : ℕ)
    → ℕ^ n → ℕ
⟦ p ⟧^(n) xs = value-at (execution-from-state (INIT-STATE xs) p) X₀

-- Ejemplos
_ : ⟦ empty-program ⟧^(2) (23 , 4) ＝ 0 
_ = refl _

_ : ⟦ eg-LOOP ⟧^(2) (23 , 4) ＝ 27
_ = refl _

-- Lema que será útil para probar propiedades.
loop-n-times-is-additon : (n : ℕ) → (y₀ : ℕ) → (xs : List ℕ) → loop-n-times n (y₀ :: xs) (INC X₀ :: END) ＝ (y₀ + n :: xs)
loop-n-times-is-additon  0       y₀ xs = refl (y₀ :: xs)
loop-n-times-is-additon (succ n) y₀ xs = (loop-n-times-is-additon n (y₀ + 1) xs) ∙ (ap (_:: xs) (Peano.succ+y y₀ n))

-- Proposición: la función de aridad 2 calculada por eg-LOOP es la suma de los
-- parámetros de entrada.
eg-LOOP-is-addition : (x y : ℕ) → ⟦ eg-LOOP ⟧^(2) (x , y) ＝ x + y 
eg-LOOP-is-addition x y = 
    ⟦ eg-LOOP ⟧^ 2 (x , y) 
        ＝⟨ refl _ ⟩ 
    value-at (execution-from-state (INIT-STATE (x , y)) eg-LOOP) X₀
        ＝⟨ ap (λ t → value-at t X₀) final-state ⟩ 
    value-at ((x + y) :: x :: y :: []) X₀
        ＝⟨ refl _ ⟩ 
    x + y
    ∎ where

    -- Seguimiento de la ejecución del programa.
    final-state : execution-from-state (INIT-STATE (x , y)) eg-LOOP ＝ (x + y) :: x :: y :: []
    final-state = 
        execution-from-state (INIT-STATE (x , y)) eg-LOOP 
            ＝⟨ refl _ ⟩ 
        execution-from-state (0 :: x :: y :: []) eg-LOOP 
            ＝⟨ refl _ ⟩ 
        execution-from-state (loop-n-times x (0 :: x :: y :: []) (INC X₀ :: END)) (program-from 1 eg-LOOP)
            ＝⟨ ap (λ t → execution-from-state t (program-from 1 eg-LOOP)) (loop-n-times-is-additon x 0 (x :: y :: [])) ⟩ 
        execution-from-state ((0 + x) :: x :: y :: []) (program-from 1 eg-LOOP)
            ＝⟨ refl _ ⟩ 
        loop-n-times y (0 + x :: x :: y :: []) (INC X₀ :: END)
            ＝⟨ loop-n-times-is-additon y (0 + x) (x :: y :: []) ⟩ 
        0 + x + y :: x :: y :: []
            ＝⟨ ap (λ t → t + y :: x :: y :: []) (Peano.zero+n x) ⟩ 
        x + y :: x :: y :: []
        ∎

-- 
-- 3. Funciones LOOP-computables 
--

-- 3.1. Una función f de aridad n se dice LOOP-computable si existe un
-- LOOP-programa p tal que la función de aridad n calculada por p es f.
LOOP-computableⁿ : (n : ℕ) → (ℕ^ n → ℕ) → 𝓤₀ ̇ 
LOOP-computableⁿ n f = Σ p ꞉ LOOP-program , ⟦ p ⟧^(n) ＝ f

-- Podemos omitir la aridad.
LOOP-computable : {n : ℕ} → (ℕ^ n → ℕ) → 𝓤₀ ̇ 
LOOP-computable {n} = LOOP-computableⁿ n

-- Como proposición:
LOOP-computableⁿ-prop : (n : ℕ) → (ℕ^ n → ℕ) → 𝓤₀ ̇ 
LOOP-computableⁿ-prop n f = ∥ LOOP-computableⁿ n f ∥

LOOP-computable-prop : {n : ℕ} → (ℕ^ n → ℕ) → 𝓤₀ ̇ 
LOOP-computable-prop {n} = LOOP-computableⁿ-prop n

-- Ejemplo:
uncurry-addition-is-LOOP-computable : LOOP-computable uncurry-addition
uncurry-addition-is-LOOP-computable = eg-LOOP , (funext (λ x → eg-LOOP-is-addition (pr₁ x) (pr₂ x)))


--
-- 4. Las funciones primitivas recursivas son LOOP-computables
--

-- 4.1. Funciones calculadas por LOOP-programas limpiamente

-- Para probar que toda función recursiva primitva es LOOP-computable, vamos a
-- probar que las funciones básicas son LOOP-computables, y que ser 
-- LOOP-computable es cerrado por composición y recursión. Usando 𝓟𝓡-induction,
-- se tiene.

-- En realidad, probaremos primero que toda función recursiva primitiva es 
-- calculada por un LOOP-programa limpiamente

-- Un LOOP-programa p calcula una función f : ℕ^ n → ℕ limpiamente si la
-- función de aridad n calculada por p es f, y además, en el cálculo de la 
-- función ⟦ p ⟧^(n), el valor final de las variables X 1 hasta X n es el mismo
-- que tenían inicialmente. Además, suponemos que en las restantes variables
-- que aparecen en p y no sean X₀, el valor inicial es 0, e imponemos que al
-- finalizar, su valor sea 0 también. Estas variables, por tanto, servirán como
-- variables auxiliares.

-- Calcula el mayor índice que aparece en una variable del programa. Convenimos
-- que en el programa vacío vale 0.
largest-index : LOOP-program → ℕ 
largest-index []                      = 0
largest-index (CLEAR (X n) :: p)      = max n (largest-index p)
largest-index (INC (X n) :: p)        = max n (largest-index p)
largest-index ((LOOP X n DO p') :: p) = max n (max (largest-index p') (largest-index p))

-- Una función f de aridad n es calculada por un LOOP-programa limpiamente si
-- existe un LOOP-programa p para el cual:
--      - La función ⟦ p ⟧^(n) es f. 
--      - Para una entrada xs = (x₁, ..., xₙ), si consideramos el estado 
--        inicial 0 :: x₁ :: ... :: xₙ :: 0 :: ... :: 0, rellenando con 0 hasta
--        que se ponga a 0 la variable con índice más grande que aparece en p,
--        el estado resultante tras ejecutar p es el mismo.
LOOP-computable-cleanly : {n : ℕ} → (ℕ^ n → ℕ) → 𝓤₀ ̇ 
LOOP-computable-cleanly {n} f = Σ p ꞉ LOOP-program , (((xs : ℕ^ n) → 
    execution-from-state ((INIT-STATE xs) concat (n-zeros-list ((largest-index p) ∸ n))) p
        ＝ (f xs :: INIT-STATE' xs) concat (n-zeros-list ((largest-index p) ∸ n)))
    ) 

-- Comportamiento de clear-value en un estado 
clear-value-sets-value-to-zero : (σ : STATE) → (r r' : ℕ) → 
    value-at (clear-value σ (X r)) (X r') ＝ if (ℕ-has-decidable-equality r r') then 0 else (value-at σ (X r'))
clear-value-sets-value-to-zero [] r r' = (b-or-b-then-b (ℕ-has-decidable-equality r r') 0) ⁻¹
clear-value-sets-value-to-zero (x :: σ)  0        0        = refl 0
clear-value-sets-value-to-zero (x :: σ)  0       (succ r') = refl _
clear-value-sets-value-to-zero (x :: σ) (succ r)  0        = refl x
clear-value-sets-value-to-zero (x :: σ) (succ r) (succ r') = (
    value-at (clear-value σ (X r)) (X r') 
        ＝⟨ clear-value-sets-value-to-zero σ r r' ⟩ 
    if ℕ-has-decidable-equality r r' then 0 else value-at σ (X r') 
        ∎) ∙ (if-dec-eqℕ r r' 0 (value-at σ (X r') )) 

-- Comportamiento de inc-value en un estado
inc-value-increments-value : (σ : STATE) → (r r' : ℕ) → 
    value-at (inc-value σ (X r)) (X r') ＝ if (ℕ-has-decidable-equality r r') then (succ (value-at σ (X r'))) else (value-at σ (X r'))
inc-value-increments-value []        0        0        = refl 1
inc-value-increments-value []        0       (succ r') = refl 0
inc-value-increments-value []       (succ r)         0 = refl 0
inc-value-increments-value []       (succ r) (succ r') = inc-value-increments-value [] r r' ∙ (if-dec-eqℕ r r' 1 0)
inc-value-increments-value (x :: σ)  0        0        = refl (succ x)
inc-value-increments-value (x :: σ)  0       (succ r') = refl (value-at σ (X r'))
inc-value-increments-value (x :: σ) (succ r)  0        = refl x
inc-value-increments-value (x :: σ) (succ r) (succ r') = inc-value-increments-value σ r r' ∙ (if-dec-eqℕ r r' (succ (value-at σ (X r'))) (value-at σ (X r')))

-- Añadir ceros a una lista no cambia los valores 
append-zeroes-does-not-change-values : (k : ℕ) → (σ : STATE) → (r : ℕ)
    → value-at σ (X r) ＝ value-at (σ concat (n-zeros-list k)) (X r) 
append-zeroes-does-not-change-values  0       []        _       = refl 0
append-zeroes-does-not-change-values (succ k) []        0       = refl 0
append-zeroes-does-not-change-values (succ k) []       (succ r) = append-zeroes-does-not-change-values k (0 :: []) (succ r)
append-zeroes-does-not-change-values  0       (x :: σ)  0       = refl x
append-zeroes-does-not-change-values  0       (x :: σ) (succ r) = append-zeroes-does-not-change-values zero σ r
append-zeroes-does-not-change-values (succ k) (x :: σ)  0       = refl x
append-zeroes-does-not-change-values (succ k) (x :: σ) (succ r) = append-zeroes-does-not-change-values (succ k) σ r

-- Dos estados con los mismos valores tienen la misma ejecución
same-values-same-execution : (p : LOOP-program) → (k : ℕ) → (σ τ : STATE) 
    → ((k' : ℕ) → value-at σ (X k') ＝ value-at τ (X k'))
    → value-at (execution-from-state σ p) (X k) ＝ value-at (execution-from-state τ p) (X k)
same-values-same-execution [] k σ τ same-values = same-values k
same-values-same-execution (CLEAR (X x) :: p) k σ τ same-values = same-values-same-execution p k (clear-value σ (X x)) (clear-value τ (X x)) λ k' → 
    value-at (clear-value σ (X x)) (X k') 
        ＝⟨ clear-value-sets-value-to-zero σ x k' ⟩ 
    if (ℕ-has-decidable-equality x k') then 0 else (value-at σ (X k'))
        ＝⟨ ap (if (ℕ-has-decidable-equality x k') then 0 else_) (same-values k') ⟩ 
    if (ℕ-has-decidable-equality x k') then 0 else (value-at τ (X k'))
        ＝⟨ (clear-value-sets-value-to-zero τ x k') ⁻¹ ⟩ 
    value-at (clear-value τ (X x)) (X k') 
    ∎
same-values-same-execution (INC (X x) :: p) k σ τ same-values = same-values-same-execution p k (inc-value σ (X x)) (inc-value τ (X x)) λ k' → 
    value-at (inc-value σ (X x)) (X k') 
        ＝⟨ inc-value-increments-value σ x k' ⟩ 
    if (ℕ-has-decidable-equality x k') then (succ (value-at σ (X k'))) else (value-at σ (X k'))
        ＝⟨ ap (if (ℕ-has-decidable-equality x k') then (succ (value-at σ (X k'))) else_) (same-values k') ⟩ 
    if (ℕ-has-decidable-equality x k') then (succ (value-at σ (X k'))) else (value-at τ (X k'))
        ＝⟨ ap (if (ℕ-has-decidable-equality x k') then_else (value-at τ (X k'))) (ap succ (same-values k')) ⟩ 
    if (ℕ-has-decidable-equality x k') then (succ (value-at τ (X k'))) else (value-at τ (X k'))
        ＝⟨ (inc-value-increments-value τ x k') ⁻¹ ⟩ 
    value-at (inc-value τ (X x)) (X k') 
    ∎
same-values-same-execution ((LOOP (X x) DO p') :: p) k σ τ same-values = same-values-same-execution p k (loop-n-times (value-at σ (X x)) σ p') (loop-n-times (value-at τ (X x)) τ p') 
    λ k' → same-values-same-loop-execution p' k σ τ same-values (value-at σ (X x)) k' ∙ ap (λ n → value-at (loop-n-times n τ p') (X k')) (same-values x) where
    same-values-same-loop-execution : (p' : LOOP-program) → (k : ℕ) → (σ τ : STATE) 
        → ((k' : ℕ) → value-at σ (X k') ＝ value-at τ (X k'))
        → (n : ℕ) → (k' : ℕ)
        → value-at (loop-n-times n σ p') (X k') ＝ value-at (loop-n-times n τ p') (X k')
    same-values-same-loop-execution p' k σ τ same-values zero k' = same-values k'
    same-values-same-loop-execution p' k σ τ same-values (succ n) k' = same-values-same-loop-execution p' k (execution-from-state σ p') (execution-from-state τ p') (λ k' → same-values-same-execution p' k' σ τ same-values) n k'

-- Añadir ceros a la entrada inical no cambia ningún valor tras la ejecución
append-zeros-does-not-change-values-after-execution : {n : ℕ} → (p : LOOP-program) → (k : ℕ) → (xs : ℕ^ n) 
    → (r : ℕ)
    → value-at (execution-from-state (INIT-STATE xs) p) (X r)
        ＝ value-at (execution-from-state ((INIT-STATE xs) concat (n-zeros-list k)) p) (X r)
append-zeros-does-not-change-values-after-execution {n} p k xs r = same-values-same-execution p r (INIT-STATE xs) (INIT-STATE xs concat n-zeros-list k) (append-zeroes-does-not-change-values k (INIT-STATE xs))

-- Añadir ceros a la entrada inicial no cambia la salida del programa
append-zeros-does-not-change-final-value : {n : ℕ} → (p : LOOP-program) → (k : ℕ) → (xs : ℕ^ n) 
    → value-at (execution-from-state (INIT-STATE xs) p) X₀
        ＝ value-at (execution-from-state ((INIT-STATE xs) concat (n-zeros-list k)) p) X₀
append-zeros-does-not-change-final-value {n} p k xs = append-zeros-does-not-change-values-after-execution p k xs 0

-- LOOP-program-is-clean : LOOP-program → 𝓤₀ ̇ 
-- LOOP-program-is-clean p = (x₀ : ℕ) → (σ : STATE) → Σ k ꞉ ℕ , Σ y₀ ꞉ ℕ , 
--     execution-from-state (x₀ :: σ) p ＝ (y₀ :: σ) concat (n-zeros-list k)

-- Toda función que es LOOP-computable limpiamente es LOOP-computable.
LOOP-computable-cleanly-is-LOOP-computable : {n : ℕ} → {f : ℕ^ n → ℕ}
    → LOOP-computable-cleanly f → LOOP-computable f
LOOP-computable-cleanly-is-LOOP-computable {n} {f} (p , p-c-f) = p , (funext (λ xs → 
    ⟦ p ⟧^ n xs 
        ＝⟨ refl _ ⟩ 
    value-at (execution-from-state (INIT-STATE xs) p) X₀
        ＝⟨ append-zeros-does-not-change-final-value p ((largest-index p) ∸ n) xs ⟩ 
    value-at (execution-from-state ((INIT-STATE xs) concat (n-zeros-list ((largest-index p) ∸ n))) p) X₀
        ＝⟨ ap (λ σ → value-at σ X₀) (p-c-f xs)⟩ 
    value-at ((f xs :: INIT-STATE' xs) concat (n-zeros-list ((largest-index p) ∸ n))) X₀
        ＝⟨ refl _ ⟩ 
    f xs 
    ∎))

-- 4.2. Las funciones básicas son LOOP-computables limpiamente.

-- 4.2.1. La función sucesor es LOOP-computable limpiamente.
succ-is-LOOP-computable-cleanly : LOOP-computable-cleanly succ
succ-is-LOOP-computable-cleanly = p , final-state where

    -- Programa que calcula el sucesor.
    p : LOOP-program
    p = LOOP (X 1) DO (
            INC X₀      :: 
        END)            :: 
        INC X₀          :: 
        END
    
    -- Seguimiento de la ejecución del programa.
    final-state : (x : ℕ) →
        inc-value (loop-n-times x (0 :: x :: []) (INC X₀ :: END)) X₀ ＝
        succ x :: x :: []
    final-state x = 
        inc-value (loop-n-times x (0 :: x :: []) (INC X₀ :: END)) X₀
            ＝⟨ ap (λ t → inc-value t X₀) (loop-n-times-is-additon x 0 (x :: [])) ⟩ 
        inc-value (0 + x :: x :: []) X₀
            ＝⟨ refl _ ⟩ 
        succ (0 + x) :: x :: []
            ＝⟨ ap (λ t → (succ t) :: x :: []) (Peano.zero+n x) ⟩ 
        succ x :: x :: []
        ∎

-- 4.2.1. La función sucesor es limpia LOOP-computable.
zero-fun-n-is-LOOP-computable-cleanly : (n : ℕ) → LOOP-computable-cleanly (zero-fun n) 
zero-fun-n-is-LOOP-computable-cleanly n = empty-program , λ xs → refl (zero :: INIT-STATE' xs concat []) 


-- 4.2.3. Las k proyecciones de aridad n son LOOP-computables limpiamente.
π-n-k-is-LOOP-computable-cleanly : (n : ℕ) → (k : ℕ) → {q : 1 ≤ k} → {r : k ≤ n} → LOOP-computable-cleanly (π n k {q} {r})
π-n-k-is-LOOP-computable-cleanly n k {q} {r} = p_k , final-state where

    -- Programa que calcula la proyección en la k-ésima coordenada.
    p_k : LOOP-program 
    p_k = 
        LOOP (X k) DO (
            INC X₀      :: 
        END)            ::
        END

    -- Lema 0: buscar en el vector list-n-to-vect-n xs no depende de la prueba 
    -- que xs tiene longitud n.
    lemma-0 : (n : ℕ) → (k : ℕ) → {r : 1 ≤ k} → {s : k ≤ n}
        → (xs : List ℕ) → (p q : len xs ＝ n)
        → lookup (list-n-to-vect-n (xs , p)) (!Fin k r s) ＝ lookup (list-n-to-vect-n (xs , q)) (!Fin k r s)
    lemma-0  0        k              {r} {s} xs        p q = refl (𝟘-induction (λ _ → ℕ) (!Fin k r s))
    lemma-0 (succ n)  k              {r} {s} []        p q = !𝟘 _ (lr-implication (Eqℕ-equiv-Id 0 (succ n)) p)
    lemma-0 (succ n)  0              {r} {s} (x :: xs) p q = !𝟘 _ r
    lemma-0 (succ n)  1              {r} {s} (x :: xs) p q = refl x
    lemma-0 (succ n) (succ (succ k)) {r} {s} (x :: xs) p q = lemma-0 n (succ k) xs (succ-injective p) (succ-injective q)

    -- Lema 1: value-at es lo mismo que lookup.
    lemma-1 : (n : ℕ) → (k : ℕ) → {q : 1 ≤ k} → {r : k ≤ n} → (xs : ℕ^ n) → 
        value-at (INIT-STATE xs) (X k) ＝ lookup (list-n-to-vect-n (INIT-STATE' xs , init-state'-has-len-n xs)) (!Fin k q r)
    lemma-1 n                0              {q} {r} _        = !𝟘 _ q
    lemma-1 0                1              {q} {r} _        = !𝟘 _ r
    lemma-1 1                1              {q} {r} x        = refl x
    lemma-1 (succ (succ n))  1              {q} {r} xs       = refl _
    lemma-1 0               (succ (succ k)) {q} {r} xs       = !𝟘 _ r
    lemma-1 1               (succ (succ k)) {q} {r} xs       = !𝟘 _ r
    lemma-1 (succ (succ n)) (succ (succ k)) {q} {r} (x , xs) = lemma-1 (succ n) (succ k) {q} {r} xs ∙ 
        lemma-0 (succ n) (succ k) {q} {r} (INIT-STATE' xs) 
        (init-state'-has-len-n xs) ( succ-injective (ap succ (init-state'-has-len-n xs)))
    
    -- Lema 2: lookup es lo mismo que una proyección.
    lemma-2 : (n : ℕ) → (k : ℕ) → {q : 1 ≤ k} → {r : k ≤ n} → (xs : ℕ^ n)
        → lookup (list-n-to-vect-n (INIT-STATE' xs , init-state'-has-len-n xs)) (!Fin k q r) ＝ π n k {q} {r} xs
    lemma-2 n                0              {q} {r} _        = !𝟘 _ q
    lemma-2 0               (succ k)        {q} {r} _        = refl (𝟘-induction (λ _ → ℕ) (!Fin (succ k) q r))
    lemma-2 1                1              {q} {r} x        = refl x
    lemma-2 1               (succ (succ k)) {q} {r} x        = !𝟘 _ r
    lemma-2 (succ (succ n))  1              {q} {r} xs       = refl _
    lemma-2 (succ (succ n)) (succ (succ k)) {q} {r} (x , xs) = 
        (lemma-0 (succ n) (succ k) {q} {r} (INIT-STATE' xs) (succ-injective (ap succ (init-state'-has-len-n xs))) ( init-state'-has-len-n xs)) 
            ∙ lemma-2 (succ n) (succ k) {q} {r} xs

    -- Lema 3: value-at X k es una proyección.
    lemma-3 : (xs : ℕ^ n) → value-at (INIT-STATE xs) (X k) ＝ π n k {q} {r} xs
    lemma-3 xs = lemma-1 n k {q} {r} xs ∙ (lemma-2 n k {q} {r} xs)

    -- Seguimiento de la ejecución del programa.
    final-state : (xs : ℕ^ n)
        → execution-from-state ((INIT-STATE xs) concat n-zeros-list (max k 0 ∸ n)) p_k
        ＝ (π n k {q} {r} xs :: INIT-STATE' xs) concat n-zeros-list (max k 0 ∸ n)
    final-state xs = 
        execution-from-state ((INIT-STATE xs) concat n-zeros-list (max k 0 ∸ n)) p_k
            ＝⟨ ap (λ t → execution-from-state (INIT-STATE xs concat t) p_k ) list-is-empty ⟩ 
        execution-from-state (INIT-STATE xs concat []) p_k 
            ＝⟨ ap (λ t → execution-from-state t p_k) ( (INIT-STATE xs) concat-[]) ⟩ 
        execution-from-state (INIT-STATE xs) p_k 
            ＝⟨ refl _ ⟩
        loop-n-times (value-at (INIT-STATE xs) (X k)) (INIT-STATE xs) (INC X₀ :: END) 
            ＝⟨ loop-n-times-is-additon (value-at (INIT-STATE xs) (X k)) 0 (INIT-STATE' xs) ⟩ 
        0 + value-at (INIT-STATE xs) (X k) :: INIT-STATE' xs
            ＝⟨ ap (_:: INIT-STATE' xs) (Peano.zero+n (value-at (INIT-STATE xs) (X k))) ⟩ 
        value-at (INIT-STATE xs) (X k) :: INIT-STATE' xs
            ＝⟨ ap (_:: INIT-STATE' xs) (lemma-3 xs) ⟩ 
        π n k {q} {r} xs :: INIT-STATE' xs
            ＝⟨ ((π n k {q} {r} xs :: INIT-STATE' xs) concat-[]) ⁻¹ ⟩ 
        π n k {q} {r} xs :: INIT-STATE' xs concat []
            ＝⟨ ap (λ t → π n k {q} {r} xs :: INIT-STATE' xs concat t) (list-is-empty ⁻¹) ⟩ 
        π n k {q} {r} xs :: INIT-STATE' xs concat n-zeros-list (max k 0 ∸ n)
        ∎ where

        is-zero : max k 0 ∸ n ＝ 0 
        is-zero = 
            max k 0 ∸ n
                ＝⟨ ap (_∸ n) (max-x-zero-is-x k) ⟩ 
            k ∸ n 
                ＝⟨ x∸≤-is-zero k n r ⟩ 
            0
            ∎

        list-is-empty : n-zeros-list (max k 0 ∸ n) ＝ []
        list-is-empty = ap n-zeros-list is-zero

-- 4.3. LOOP-computable es cerrado por composición

-- clear-value solo afecta a las succ (largest-index p) posiciones.
clear-value-changes-succ-largest-index-p-positions : (σ τ : STATE)
    -- → len σ ＝ succ (largest-index p) 
    -- k ≤ largest-index p
    → (k : ℕ) → (succ k ≤ len σ)
    → clear-value (σ concat τ) (X k) ＝ (clear-value σ (X k)) concat τ 
clear-value-changes-succ-largest-index-p-positions []       _  _       k≤large = !𝟘 _ k≤large
clear-value-changes-succ-largest-index-p-positions (x :: σ) τ  0       k≤large = refl (0 :: σ concat τ)
clear-value-changes-succ-largest-index-p-positions (x :: σ) τ (succ k) k≤large = ap (x ::_) (clear-value-changes-succ-largest-index-p-positions σ τ k k≤large)

-- clear-value no cambia la longitud de un estado.
clear-value-preserves-len : (σ : STATE) → (k : ℕ)
    → len (clear-value σ (X k)) ＝ len σ  
clear-value-preserves-len []        0       = refl 0
clear-value-preserves-len []       (succ k) = refl 0
clear-value-preserves-len (x :: σ)  0       = refl (succ (len σ))
clear-value-preserves-len (x :: σ) (succ k) = ap succ (clear-value-preserves-len σ k)

-- inc-value solo afecta a las succ (largest-index p) posiciones.
inc-value-changes-succ-largest-index-p-positions : (σ τ : STATE)
    → (k : ℕ) → (succ k ≤ len σ)
    → inc-value (σ concat τ) (X k) ＝ (inc-value σ (X k)) concat τ 
inc-value-changes-succ-largest-index-p-positions []       _  _       k≤large = !𝟘 _ k≤large
inc-value-changes-succ-largest-index-p-positions (x :: σ) τ  0       k≤large = refl (succ x :: σ concat τ)
inc-value-changes-succ-largest-index-p-positions (x :: σ) τ (succ k) k≤large = ap (x ::_) (inc-value-changes-succ-largest-index-p-positions σ τ k k≤large)

-- inc-value no cambia la longitud de un estado suficientemente grande
inc-value-preserves-len : (σ : STATE) → (k : ℕ)
    → (succ k ≤ len σ)
    → len (inc-value σ (X k)) ＝ len σ  
inc-value-preserves-len [] _ succ-k≤len-σ = !𝟘 _ succ-k≤len-σ
inc-value-preserves-len (x :: σ) 0 succ-k≤len-σ = refl (succ (len σ))
inc-value-preserves-len (x :: σ) (succ k) succ-k≤len-σ = ap succ (inc-value-preserves-len σ k succ-k≤len-σ)

-- value-at solo afecta a las primeras n posiciones.
value-at-only-first-n-positions : (σ τ : STATE) → (k : ℕ) → (succ k ≤ len σ)
    → value-at (σ concat τ) (X k) ＝ value-at σ (X k)
value-at-only-first-n-positions  []      _  _       k-not-large = !𝟘 _ k-not-large
value-at-only-first-n-positions (x :: σ) _  0       k-not-large = refl x
value-at-only-first-n-positions (x :: σ) τ (succ k) k-not-large = value-at-only-first-n-positions σ τ k k-not-large

-- Ejecutar un programa sobre un estado lo suficientemente grande no aumenta la
-- longitud del estado
execution-from-large-state-doesn't-change-size : (p : LOOP-program) → (σ : STATE) 
    → len σ ≥ succ (largest-index p)
    → len (execution-from-state σ p) ＝ len σ
execution-from-large-state-doesn't-change-size [] σ σ-large = refl _
execution-from-large-state-doesn't-change-size (CLEAR (X x) :: p) σ σ-large = (execution-from-large-state-doesn't-change-size p (clear-value σ (X x)) 
    (transport (succ (largest-index p) ≤_) (clear-value-preserves-len σ x ⁻¹) (≤-transitive {succ (largest-index p)} {succ (max x (largest-index p))} {len σ} (y≤max x (largest-index p)) σ-large))) 
    ∙ (clear-value-preserves-len σ x )
execution-from-large-state-doesn't-change-size (INC (X x) :: p) σ σ-large = execution-from-large-state-doesn't-change-size p (inc-value σ (X x)) 
    (transport (succ (largest-index p) ≤_) (aux-eq ⁻¹) (≤-transitive {succ (largest-index p)} {succ (max x (largest-index p))} {len σ} (y≤max x (largest-index p)) σ-large)) 
    ∙ aux-eq where
        aux-eq : len (inc-value σ (X x)) ＝ len σ
        aux-eq = inc-value-preserves-len σ x (≤-transitive {succ x} {succ (max x (largest-index p))} {len σ} (x≤max x (largest-index p)) σ-large)
execution-from-large-state-doesn't-change-size ((LOOP X x DO p') :: p) σ σ-large = execution-from-large-state-doesn't-change-size p (loop-n-times (value-at σ (X x)) σ p')
    (transport (succ (largest-index p) ≤_) (aux-eq ⁻¹) 
    (≤-transitive {succ (largest-index p)} {succ (max x (max (largest-index p') (largest-index p)))} {len σ} 
        (z≤y-then-z≤max-x-y x (max (largest-index p') (largest-index p)) (largest-index p) (y≤max (largest-index p') (largest-index p))) σ-large)) 
    ∙ aux-eq where

    lemma : (n : ℕ) → (p : LOOP-program) → (σ : STATE) 
        → len σ ≥ succ (largest-index p)
        → len (loop-n-times n σ p) ＝ len σ
    lemma 0 p σ _ = refl (len σ)
    lemma (succ n) p σ q = lemma n p (execution-from-state σ p) 
        (transport (succ (largest-index p) ≤_) ((execution-from-large-state-doesn't-change-size p σ q) ⁻¹) q) 
        ∙ (execution-from-large-state-doesn't-change-size p σ q)

    largest-index-p'≤max-max : largest-index p' ≤ max x (max (largest-index p') (largest-index p))
    largest-index-p'≤max-max = z≤y-then-z≤max-x-y x (max (largest-index p') (largest-index p)) (largest-index p') (x≤max (largest-index p') (largest-index p))

    aux-eq : len (loop-n-times (value-at σ (X x)) σ p') ＝ len σ
    aux-eq = lemma (value-at σ (X x)) p' σ (≤-transitive {succ (largest-index p')} { succ (max x (max (largest-index p') (largest-index p)))} {len σ} largest-index-p'≤max-max σ-large)


-- Añadir valores tras la última variable del programa no afecta a la 
-- ejecución.
variables-after-largest-variable-don't-matter' : (p : LOOP-program) → (σ τ : STATE)
    → len σ ≥ succ (largest-index p) 
    → execution-from-state (σ concat τ) p ＝ (execution-from-state σ p) concat τ
variables-after-largest-variable-don't-matter' []                      σ τ σ-large = refl (σ concat τ)
variables-after-largest-variable-don't-matter' (CLEAR (X x) :: p)      σ τ σ-large = 
    execution-from-state (clear-value (σ concat τ) (X x)) p
        ＝⟨ ap (λ s → execution-from-state s p) (clear-value-changes-succ-largest-index-p-positions σ τ x succ-x≤len-σ) ⟩ 
    execution-from-state (clear-value σ (X x) concat τ) p 
        ＝⟨ variables-after-largest-variable-don't-matter' p (clear-value σ (X x)) τ succ-largest≤len-clear ⟩ 
    execution-from-state (clear-value σ (X x)) p concat τ
    ∎ where

    succ-x≤len-σ : succ x ≤ len σ 
    succ-x≤len-σ = ≤-transitive {succ x} {succ (max x (largest-index p))} {len σ} (x≤max x (largest-index p))  σ-large

    succ-largest≤len-clear : succ (largest-index p) ≤ len (clear-value σ (X x))
    succ-largest≤len-clear = transport (succ (largest-index p) ≤_) (clear-value-preserves-len σ x ⁻¹) (
        ≤-transitive {succ (largest-index p)} {succ (max x (largest-index p))} {len σ} (y≤max x (largest-index p)) σ-large)

variables-after-largest-variable-don't-matter' (INC (X x) :: p)        σ τ σ-large = execution-from-state (inc-value (σ concat τ) (X x)) p
        ＝⟨ ap (λ s → execution-from-state s p) (inc-value-changes-succ-largest-index-p-positions σ τ x succ-x≤len-σ) ⟩ 
    execution-from-state (inc-value σ (X x) concat τ) p
        ＝⟨ variables-after-largest-variable-don't-matter' p (inc-value σ (X x)) τ succ-largest≤len-inc ⟩ 
    execution-from-state (inc-value σ (X x)) p concat τ
    ∎ where

    succ-x≤len-σ : succ x ≤ len σ 
    succ-x≤len-σ = ≤-transitive {succ x} {succ (max x (largest-index p))} {len σ} (x≤max x (largest-index p))  σ-large

    succ-max≤len-σ : succ (max x 0) ≤ len σ 
    succ-max≤len-σ = transport (λ t → succ t ≤ len σ) (max-refl x 0 ⁻¹) succ-x≤len-σ


    succ-largest≤len-inc : succ (largest-index p) ≤ len (inc-value σ (X x))
    succ-largest≤len-inc = transport (succ (largest-index p) ≤_) (execution-from-large-state-doesn't-change-size (INC (X x) :: END) σ succ-max≤len-σ  ⁻¹) 
        (≤-transitive {succ (largest-index p)} {succ (max x (largest-index p))} {len σ} (y≤max x (largest-index p)) σ-large)

variables-after-largest-variable-don't-matter' ((LOOP X x DO p') :: p) σ τ σ-large = 
    (execution-from-state (loop-n-times (value-at (σ concat τ) (X x)) (σ concat τ) p') p
        ＝⟨ ap (λ t → execution-from-state (loop-n-times t (σ concat τ) p') p) (value-at-only-first-n-positions σ τ x succ-x≤len-σ) ⟩ 
    execution-from-state (loop-n-times (value-at σ (X x)) (σ concat τ) p') p
        ＝⟨ ap (λ s → execution-from-state s p) (loop-n-times-concats-out p' σ τ len-σ≥succ-largest-p' (value-at σ (X x))) ⟩ 
    execution-from-state (loop-n-times (value-at σ (X x)) σ p' concat τ) p
    ∎)  ∙ variables-after-largest-variable-don't-matter' p (loop-n-times (value-at σ (X x)) σ p') τ 
            (transport (succ (largest-index p) ≤_) (execution-from-large-state-doesn't-change-size ((LOOP X x DO p') :: END) σ len-σ≥-succ ⁻¹) succ-largest≤len-σ) where

    succ-x≤len-σ : succ x ≤ len σ 
    succ-x≤len-σ = ≤-transitive {succ x} {succ (max x (max (largest-index p') (largest-index p)))} {len σ} (x≤max x (max (largest-index p') (largest-index p))) σ-large

    succ-largest≤len-σ : succ (largest-index p) ≤ len σ
    succ-largest≤len-σ = ≤-transitive {succ (largest-index p)} {succ (max x (max (largest-index p') (largest-index p)))} {len σ} 
        (z≤y-then-z≤max-x-y x (max (largest-index p') (largest-index p)) (largest-index p) (y≤max (largest-index p') (largest-index p))) σ-large

    largest-index-p'≤max : largest-index p' ≤ max (largest-index p') (largest-index p)
    largest-index-p'≤max = x≤max (largest-index p') (largest-index p)

    len-σ≥-succ : len σ ≥ succ (max x (max (largest-index p') 0))
    len-σ≥-succ = transport (λ t → succ (max x t) ≤ len σ) (max-refl (largest-index p') 0 ⁻¹) 
        (≤-transitive {succ (max x (largest-index p'))} {succ (max x (max (largest-index p') (largest-index p)))} {len σ} 
        (y≤z-then-max-x-y≤max-x-z x (largest-index p') (max (largest-index p') (largest-index p)) (x≤max (largest-index p') (largest-index p))) σ-large)

    largest-index-p'≤max-max : largest-index p' ≤ max x (max (largest-index p') (largest-index p))
    largest-index-p'≤max-max = z≤y-then-z≤max-x-y x (max (largest-index p') (largest-index p)) (largest-index p') largest-index-p'≤max

    len-σ≥succ-largest-p' : len σ ≥ succ (largest-index p')
    len-σ≥succ-largest-p' = ≤-transitive {succ (largest-index p')} { succ (max x (max (largest-index p') (largest-index p)))} {len σ} largest-index-p'≤max-max σ-large

    loop-n-times-concats-out : (p : LOOP-program) → (σ τ : STATE) → (len σ ≥ succ (largest-index p) )
        → (n : ℕ) → loop-n-times n (σ concat τ) p ＝ (loop-n-times n σ p) concat τ
    loop-n-times-concats-out _ _ _ _        0       = refl _
    loop-n-times-concats-out p σ τ σ-large (succ n) = ap (λ t → loop-n-times n t p) (variables-after-largest-variable-don't-matter' p σ τ σ-large) 
        ∙ loop-n-times-concats-out p (execution-from-state σ p) τ (transport (succ (largest-index p) ≤_) (execution-from-large-state-doesn't-change-size p σ σ-large ⁻¹) σ-large) n

-- variables-after-largest-variable-don't-matter : (p : LOOP-program) → (σ τ : STATE)
--     → len σ ＝ succ (largest-index p) 
--     → execution-from-state (σ concat τ) p ＝ (execution-from-state σ p) concat τ
-- variables-after-largest-variable-don't-matter p σ τ σ-large = variables-after-largest-variable-don't-matter' p σ τ (transport (len σ ≥_) σ-large (≤-reflexive (len σ)))

-- Podemos cononcer la ejecución de un programa que calcula una función 
-- primitiva recursiva limpiamente
execution-of-LOOP-computable-cleanly-with-aux-variables :
    {n : ℕ} → {f : ℕ^ n → ℕ} → {c : LOOP-computable-cleanly f}
    → (xs : ℕ^ n) → (τ : STATE) 
    → execution-from-state (((INIT-STATE xs) concat (n-zeros-list ((largest-index (pr₁ c)) ∸ n))) concat τ) (pr₁ c)
        ＝ ((f xs :: INIT-STATE' xs) concat (n-zeros-list ((largest-index (pr₁ c)) ∸ n))) concat τ
execution-of-LOOP-computable-cleanly-with-aux-variables {n} {f} {c} xs τ = 
    execution-from-state (σ concat τ) p 
        ＝⟨ variables-after-largest-variable-don't-matter' p σ τ len-σ≥succ-largest-p ⟩
    execution-from-state σ p concat τ
        ＝⟨ ap (_concat τ) ((pr₂ c) xs) ⟩ 
    (f xs :: INIT-STATE' xs concat n-zeros-list (largest-index p ∸ n)) concat τ
    ∎ where

    p = (pr₁ c)

    σ = (INIT-STATE xs) concat (n-zeros-list ((largest-index p) ∸ n))

    len-σ : len σ ＝ succ (max (largest-index p) n) 
    len-σ = len-concat-is-sum-len (INIT-STATE xs) (n-zeros-list (largest-index p ∸ n)) 
        ∙ (
        succ (len (INIT-STATE' xs)) + len (n-zeros-list (largest-index p ∸ n))
            ＝⟨ ap (succ (len (INIT-STATE' xs)) +_) (len-zeros (largest-index p ∸ n)) ⟩ 
        succ (len (INIT-STATE' xs)) + (largest-index p ∸ n)
            ＝⟨ ap (λ t → succ t + (largest-index p ∸ n)) (init-state'-has-len-n xs) ⟩ 
        succ n + (largest-index p ∸ n)
            ＝⟨ Peano.succ+y n (largest-index p ∸ n) ⟩ 
        succ (n + (largest-index p ∸ n))
            ＝⟨ ap succ (diff-gets-max n (largest-index p)) ⟩ 
        succ (max n (largest-index p))
            ＝⟨ ap succ (max-refl n (largest-index p)) ⟩ 
        succ (max (largest-index p) n)
        ∎)

    len-σ≥succ-largest-p : len σ ≥ succ (largest-index p)
    len-σ≥succ-largest-p = ≤-transitive {succ (largest-index p)} {succ (max (largest-index p) n)} {len σ} (x≤max (largest-index p) n) 
        (transport (max (largest-index p) n ≤_) (succ-injective (len-σ ⁻¹)) (≤-reflexive (max (largest-index p) n)))


-- Versión 2
execution-of-LOOP-computable-cleanly-with-aux-variables-2 :
    {n : ℕ} → {f : ℕ^ n → ℕ} → (c : LOOP-computable-cleanly f)
    → (xs : ℕ^ n) 
    → (k : ℕ) → (k ≥ (largest-index (pr₁ c)) ∸ n)
    → (τ : STATE) 
    → execution-from-state (((INIT-STATE xs) concat (n-zeros-list k)) concat τ) (pr₁ c)
        ＝ ((f xs :: INIT-STATE' xs) concat (n-zeros-list k)) concat τ
execution-of-LOOP-computable-cleanly-with-aux-variables-2 {n} {f} c xs k k≤max τ = 
    execution-from-state (σ₁ concat τ) p
        ＝⟨ ap (λ t → execution-from-state (((INIT-STATE xs) concat (n-zeros-list t)) concat τ) p) (q ⁻¹) ⟩ 
    execution-from-state (((INIT-STATE xs) concat (n-zeros-list (i-max + r))) concat τ) p
        ＝⟨ ap (λ l → execution-from-state (((INIT-STATE xs) concat l) concat τ) p) ((concat-zeros i-max r) ⁻¹) ⟩ 
    execution-from-state (((INIT-STATE xs) concat (n-zeros-list i-max) concat (n-zeros-list r)) concat τ) p
        ＝⟨ ap (λ l → execution-from-state (l concat τ) p) (concat-associative (INIT-STATE xs) (n-zeros-list i-max) (n-zeros-list r)) ⟩ 
    execution-from-state ((σ₂ concat (n-zeros-list r)) concat τ) p
        ＝⟨ ap (λ l → execution-from-state l p) ((concat-associative σ₂ (n-zeros-list r) τ) ⁻¹) ⟩ 
    execution-from-state (σ₂ concat τ₂) p
        ＝⟨ execution-of-LOOP-computable-cleanly-with-aux-variables {n} {f} {c} xs τ₂ ⟩ 
    ((f xs :: INIT-STATE' xs) concat (n-zeros-list i-max)) concat τ₂
        ＝⟨ (concat-associative (f xs :: INIT-STATE' xs) (n-zeros-list i-max) τ₂) ⁻¹ ⟩ 
    (f xs :: INIT-STATE' xs) concat (n-zeros-list i-max) concat τ₂
        ＝⟨ ap ((f xs :: INIT-STATE' xs) concat_) (concat-associative (n-zeros-list i-max) (n-zeros-list r) τ) ⟩ 
    (f xs :: INIT-STATE' xs) concat ((n-zeros-list i-max) concat (n-zeros-list r)) concat τ
        ＝⟨ ap (λ l → (f xs :: INIT-STATE' xs) concat l concat τ) (concat-zeros i-max r) ⟩ 
    (f xs :: INIT-STATE' xs) concat (n-zeros-list (i-max + r)) concat τ
        ＝⟨ ap (λ t → (f xs :: INIT-STATE' xs) concat (n-zeros-list t) concat τ) q ⟩ 
    (f xs :: INIT-STATE' xs) concat (n-zeros-list k) concat τ
        ＝⟨ concat-associative (f xs :: INIT-STATE' xs) (n-zeros-list k) τ ⟩ 
    (f xs :: INIT-STATE' xs concat n-zeros-list k) concat τ
     ∎ where
    σ₁ = (INIT-STATE xs) concat (n-zeros-list k)
    p = pr₁ c

    i-max = (largest-index (pr₁ c)) ∸ n
    r,q = ≤-gets-diff i-max k k≤max 
    r = pr₁ r,q

    σ₂ = (INIT-STATE xs) concat (n-zeros-list i-max)
    τ₂ = (n-zeros-list r) concat τ

    q : i-max + r ＝ k 
    q = (Peano.+-conmutative i-max r) ∙ pr₂ r,q

-- Ejecutar programas concatenados concatena las ejecuciones.
program-concat-is-execution-composition : (p q : LOOP-program) → (σ : STATE)
    → execution-from-state σ (p concat q) ＝ execution-from-state (execution-from-state σ p) q
program-concat-is-execution-composition []                    q σ = refl _
program-concat-is-execution-composition (CLEAR x :: p)        q σ = program-concat-is-execution-composition p q (clear-value σ x)
program-concat-is-execution-composition (INC x :: p)          q σ = program-concat-is-execution-composition p q (inc-value σ x)
program-concat-is-execution-composition ((LOOP x DO p') :: p) q σ = program-concat-is-execution-composition p q (loop-n-times (value-at σ x) σ p')

-- El mayor índice de dos programas concatenados es el máximo de cada programa
largest-index-of-concat-is-max : (p p' : LOOP-program)
    → largest-index (p concat p') ＝ max (largest-index p) (largest-index p')
largest-index-of-concat-is-max [] p' = refl (largest-index p')
largest-index-of-concat-is-max (CLEAR (X x) :: p) p' = 
    max x (largest-index (p concat p'))
        ＝⟨ ap (max x) (largest-index-of-concat-is-max p p') ⟩ 
    max x (max (largest-index p) (largest-index p'))
        ＝⟨ (max-assoc x (largest-index p) (largest-index p')) ⁻¹ ⟩ 
    max (max x (largest-index p)) (largest-index p')
    ∎
largest-index-of-concat-is-max (INC (X x) :: p) p' = 
    max x (largest-index (p concat p'))
        ＝⟨ ap (max x) (largest-index-of-concat-is-max p p') ⟩ 
    max x (max (largest-index p) (largest-index p'))
        ＝⟨ (max-assoc x (largest-index p) (largest-index p')) ⁻¹ ⟩ 
    max (max x (largest-index p)) (largest-index p')
    ∎
largest-index-of-concat-is-max ((LOOP X x DO q) :: p) p' = 
    max x (max (largest-index q) (largest-index (p concat p')))
        ＝⟨ ap (λ t → max x (max (largest-index q) t)) (largest-index-of-concat-is-max p p') ⟩ 
    max x (max (largest-index q) (max (largest-index p) (largest-index p')))
        ＝⟨ ap (max x) ((max-assoc (largest-index q) (largest-index p) (largest-index p')) ⁻¹) ⟩ 
    max x (max (max (largest-index q) (largest-index p)) (largest-index p'))
        ＝⟨ (max-assoc x (max (largest-index q) (largest-index p)) (largest-index p')) ⁻¹ ⟩ 
    max (max x (max (largest-index q) (largest-index p))) (largest-index p')
    ∎

LOOP-computable-cleanly-closed-under-composition : {n k : ℕ} → {h : ℕ^ k → ℕ} 
            → (h-clean : LOOP-computable-cleanly h)
            → (gs-clean : Vect (Σ g ꞉ (ℕ^ n → ℕ) , LOOP-computable-cleanly g) k) 
            → LOOP-computable-cleanly (PR-comp h (map gs-clean pr₁))
LOOP-computable-cleanly-closed-under-composition {n} {k} {h} (p_h , h-clean) gs-clean = {!   !} where

    -- El programa que calcula la composición usa variables auxiliares. Para
    -- elegir qué variables usar, empezamos en un índice lo suficientemente
    -- grande para que así no solape con los índices de las variables de los
    -- programas para h y gs.
    i₀ : ℕ 
    i₀ = max (largest-index p_h) {!   !}

    -- Las variables a usar serán:
    --   yⱼ = i₀ + j,       con j desde 1 hasta k.
    --   zⱼ = i₀ + k + j,   con j desde 1 hasta n.
    
    yⱼ zⱼ : (j : ℕ) → VAR

    yⱼ j = X (i₀ + j)
    zⱼ j = X (i₀ + k + j)

    -- Paso 1. Calcular yⱼ = gⱼ (x₁, ..., xₙ) 
    -- Paso 1.1. Calcular gⱼ (x₁, ..., xₙ) 
    -- Paso 1.2. Almacenar el resultado en yⱼ 
    -- Paso 1.3. Borrar la variable X₀ 
    calculate-g-j : (n k : ℕ) → (gs-clean : Vect (Σ g ꞉ (ℕ^ n → ℕ) , LOOP-computable-cleanly g) k) 
        → LOOP-program
    calculate-g-j n  0        nil                      = END
    calculate-g-j n (succ k) (g , g-clean ++ gs-clean) = 
            calculate-g-j n k gs-clean 
        concat 
            pr₁ g-clean 
        concat 
            LOOP X₀ DO (
                INC (yⱼ (succ k))   ::
            END)                    :: 
            CLEAR X₀                :: 
            END
    
    p-1 = calculate-g-j n k gs-clean

    -- Paso 2. Calcular h(y₁, ..., yₖ) 
    -- Paso 2.1. Mover X j a zⱼ, con j = 1, ..., n
    -- Paso 2.2. Poner yⱼ en X j, con j = 1, ..., k
    -- Paso 2.3. Calcular h 

    move-x-j : (n k : ℕ) → LOOP-program
    move-x-j  0       k = END
    move-x-j (succ n) k = move-x-j n k concat 
        LOOP X (succ n) DO (
            INC (zⱼ (succ n))       ::
        END)                        ::
        CLEAR (X (succ n))          ::
        END 

    copy-y-j : (n k : ℕ) → LOOP-program
    copy-y-j n        0 = END
    copy-y-j n (succ k) = copy-y-j n k concat 
        LOOP (yⱼ (succ n)) DO (
            INC (X (succ n))       ::
        END)                       :: 
        END

    p-2-1 = move-x-j n k 
    p-2-2 = copy-y-j n k 
    p-2-3 = p_h

    p-2 = p-2-1 concat p-2-2 concat p-2-3

    -- Paso 3. Limpiar el programa
    -- Paso 3.1. Borrar X j, con j = 1, ..., k
    -- Paso 3.2. Restaurar zⱼ en X j
    -- Paso 3.3. Borrar los yⱼ y los zⱼ 
    -- Paso 3.3. Borrar loz zⱼ

    remove-x-j : (n k : ℕ) → LOOP-program
    remove-x-j n 0        = END
    remove-x-j n (succ k) = remove-x-j n k concat CLEAR (X (succ k)) :: END

    copy-z-j : (n k : ℕ) → LOOP-program
    copy-z-j  0       k = END
    copy-z-j (succ n) k = copy-z-j n k concat 
        LOOP (zⱼ (succ n)) DO (
            INC (X (succ n))       ::
        END)                       :: 
        END

    remove-y-j : (n k : ℕ) → LOOP-program 
    remove-y-j n 0        = END
    remove-y-j n (succ k) = remove-y-j n k concat 
        CLEAR (yⱼ (succ k)) :: END

    remove-z-j : (n k : ℕ) → LOOP-program
    remove-z-j  0       k = END
    remove-z-j (succ n) k = remove-z-j n k concat 
        CLEAR (zⱼ (succ n)) :: END
    
    p-3-1 = remove-x-j n k 
    p-3-2 = copy-z-j   n k
    p-3-3 = remove-y-j n k 
    p-3-4 = remove-z-j n k

    p-3 = p-3-1 concat p-3-2 concat p-3-3 concat p-3-4

    -- El programa es la sucesión de las partes
    p : LOOP-program
    p = p-1 concat p-2 concat p-3

    -- El índice más grande de p es i₀ + n + k 

    -- largest-of-p : largest-index p = i₀ + n + k 
    -- largest-of-p = ?

    -- Seguimiento de la ejecución del programa.
    -- final-state : (xs : ℕ^ n) → 



{-

LOOP-computable-clean-closed-under-composition : {n k : ℕ} → {h : ℕ^ k → ℕ} 
            → (h-comp : LOOP-computable-clean h)
            → (gs-comp : Vect (Σ g ꞉ (ℕ^ n → ℕ) , LOOP-computable-clean g) k) 
            → LOOP-computable-clean (PR-comp h (map gs-comp pr₁))
LOOP-computable-clean-closed-under-composition {n} {k} {h} h-comp gs-comp = {!   !} , ({!   !} , {!   !}) where

    -- Programa que calcula la composición

    -- Paso 1. Guardar los valores iniciales de entrada
    -- El programa p-shift parte de un estado x₀ :: σ y lo convierte en un estado 
    -- (x₀ :: σ) concat σ
    p-shift-r-j : (r j : ℕ) → (x₀ : ℕ) → (σ : STATE) → LOOP-program 
    p-shift-r-j r j x₀ [] = empty-program
    p-shift-r-j r j x₀ (x₁ :: σ) = (
        CLEAR (X (r + j))   :: 
        LOOP (X j) DO (
            INC (X (r + j)) :: 
        END)                :: 
        END) 
        concat p-shift-r-j r (j + 1) x₀ σ 

    p-shift : (x₀ : ℕ) → (σ : STATE) → LOOP-program 
    p-shift x₀ σ = p-shift-r-j (len (x₀ :: σ)) 1 x₀ σ

    lemma-1-p-shift : (σ : STATE) → clear-value σ (X (len σ + 1)) ＝ σ 
    lemma-1-p-shift [] = refl []
    lemma-1-p-shift (x :: σ) = ap (x ::_) (lemma-1-p-shift σ)

    lemma-2-p-shift : (σ : STATE) → (x : ℕ) 
        → loop-n-times x σ (INC (X (len σ + 1)) :: END) ＝ σ concat x :: []
    lemma-2-p-shift [] x = {!   !}
    lemma-2-p-shift (x₁ :: σ) x = {!   !}

    lemma-p-shift : (x₀ : ℕ) → (σ : STATE) 
        → execution-from-state (x₀ :: σ) (p-shift x₀ σ) ＝ x₀ :: σ concat σ
    lemma-p-shift x₀ [] = refl _
    lemma-p-shift x₀ (x₁ :: σ) = {! 
        execution-from-state (x₀ :: x₁ :: σ) (p-shift x₀ (x₁ :: σ))
        
            ＝⟨ refl _ ⟩ 

        execution-from-state
            (loop-n-times x₁ (x₀ :: x₁ :: clear-value σ (X (n_σ + 1)))
                (INC (X (n_σ + 3)) :: END))
            (p-shift-r-j (n_σ + 2) 2 x₀ σ)

            ＝⟨ ap (λ τ → execution-from-state
                (loop-n-times x₁ (x₀ :: x₁ :: τ)
                    (INC (X (n_σ + 3)) :: END))
                (p-shift-r-j (n_σ + 2) 2 x₀ σ)) (lemma-1-p-shift σ) ⟩ 

        execution-from-state
            (loop-n-times x₁ (x₀ :: x₁ :: σ) (INC (X (n_σ + 3)) :: END))
            (p-shift-r-j (n_σ + 2) 2 x₀ σ)

            ＝⟨ ap (λ t → execution-from-state t (p-shift-r-j (n_σ + 2) 2 x₀ σ)) 
                (lemma-2-p-shift (x₀ :: x₁ :: σ) x₁)    ⟩ 
        
        execution-from-state (x₀ :: x₁ :: σ concat x₁ :: []) (p-shift-r-j (n_σ + 2) 2 x₀ σ)

        ∎
      !} where
        n_σ = len σ

    p : LOOP-program
    p = {!  !}





-- 4.4. LOOP-computable es cerrado por recursión

LOOP-computable-clean-closed-under-recursion : {n : ℕ} → {g : ℕ^ n → ℕ} → {h : (ℕ^ (n + 2)) → ℕ}
            → (g-comp : LOOP-computable-clean g) → (h-comp : LOOP-computable-clean h) 
            → LOOP-computable-clean (ρ-operator g h)
LOOP-computable-clean-closed-under-recursion  {n} {g} {h} g-comp h-comp = {!   !}

-- 4.5. Teorema: toda función primitiva recursiva es LOOP-computable
𝓟𝓡-is-LOOP-computable : {n : ℕ} → (f : ℕ^ n → ℕ)
    → 𝓟𝓡 f → LOOP-computable f 
𝓟𝓡-is-LOOP-computable f f-pr = LOOP-computable-clean-is-LOOP-computable (
    𝓟𝓡-induction 
        succ-is-LOOP-computable-clean 
        zero-fun-n-is-LOOP-computable-clean 
        π-n-k-is-LOOP-computable-clean 
        LOOP-computable-clean-closed-under-composition 
        LOOP-computable-clean-closed-under-recursion 
        _ f f-pr)


-- 4.6. Teorema: toda función meramente primitiva recursiva es meramente
-- LOOP-computable
𝓟𝓡-prop-is-LOOP-computable-prop : {n : ℕ} → {f : ℕ^ n → ℕ}
    → 𝓟𝓡-prop f → LOOP-computable-prop f 
𝓟𝓡-prop-is-LOOP-computable-prop = ∥∥-recursion ∥∥-is-subsingleton (λ f-pr → ∣ 𝓟𝓡-is-LOOP-computable _ f-pr ∣)
-}
-- 
-- 5. Las funciones LOOP-computables son primitivas recursivas
--

--
-- 6. El tipo de las funciones que son meramente primitivas recursivas y el tipo 
-- de las funciones que son LOOP-computables coincide
--

