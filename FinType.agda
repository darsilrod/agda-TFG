{-# OPTIONS --without-K --exact-split --auto-inline #-}
module FinType where

open import MLTT renaming (_+_ to _⊕_)
open import List
open import Arithmetic

-- Fin n es un tipo con exactamente n elementos
Fin : ℕ → 𝓤₀ ̇ 
Fin  0       = 𝟘
Fin (succ n) = (Fin n) ⊕ 𝟙

-- zer n es el primer elemento de Fin (n + 1)
zer : (n : ℕ) → Fin (n + 1) 
zer _ = inr * 

-- Si i está entre 0 y n-1, suc n i está entre 1 y n. Con zer y suc obtenemos
-- todos los elementos de Fin (n + 1)
suc : (n : ℕ) → (i : Fin n) → Fin (n + 1)
suc _ i = inl i

-- Si tenemos un número n entre 1 y k, podemos verlo como un elemento de Fin k
!Fin : {k : ℕ} → (n : ℕ) → (1 ≤ n) → (n ≤ k) → Fin k 
!Fin {_}      0               p   = !𝟘 _ p
!Fin {0}      1               _ q = !𝟘 _ q
!Fin {succ k} 1               _ _ = zer k 
!Fin {0}      (succ (succ _)) p q = !𝟘 _ q
!Fin {succ k} (succ (succ n)) p q = suc k (!Fin (succ n) * q)

-- Aplicación de Fin n: implementar lookup para vectores
lookup : {A : 𝓤 ̇ } {n : ℕ} → Vect A n → Fin n → A 
lookup {n = 0}       xs        i      = !𝟘 _ i
lookup {n = succ n} (x ++ xs) (inr _) = x
lookup {n = succ n} (x ++ xs) (inl i) = lookup xs i
