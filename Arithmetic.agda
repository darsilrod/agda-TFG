{-# OPTIONS --without-K --exact-split --auto-inline #-}

module Arithmetic where

open import MLTT renaming (_+_ to _⊕_)


_+_ _⋆_ : ℕ → ℕ → ℕ

x + zero = x
x + succ y = succ (x + y)

x ⋆ zero = 0
x ⋆ succ y = x + x ⋆ y

infixl 20 _+_
infixl 21 _⋆_

succ-injective : {x y : ℕ} → succ x ＝ succ y → x ＝ y
succ-injective {x} {y} succx-eq-succy = (rl-implication (Eqℕ-equiv-Id x y)) (lr-implication (Eqℕ-equiv-Id (succ x) (succ y)) succx-eq-succy)


module Peano where

    zero+n : (n : ℕ) → 0 + n ＝ n 
    zero+n 0 = refl _
    zero+n (succ n) = ap succ (zero+n n)

    succ+y : (x y : ℕ) → succ x + y ＝ succ (x + y) 
    succ+y x zero = refl (succ x)
    succ+y x (succ y) = ap succ (succ+y x y)

    zero*n : (n : ℕ) → 0 ⋆ n ＝ 0 
    zero*n 0 = refl _
    zero*n (succ n) = (zero+n (0 ⋆ n)) ∙ (zero*n n)

    one*n : (n : ℕ) → 1 ⋆ n ＝ n 
    one*n zero = refl zero
    one*n (succ n) = (succ+y 0 (1 ⋆ n)) ∙ (ap succ (zero+n (1 ⋆ n))) ∙ (ap succ (one*n n))

    +-assoc : (x y z : ℕ) → x + y + z ＝ x + (y + z)
    +-assoc x y zero = refl (x + y)
    +-assoc x y (succ z) = ap succ (+-assoc x y z) 

    +-conmutative : (x y : ℕ) → x + y ＝ y + x
    +-conmutative x zero = zero+n x ⁻¹
    +-conmutative x (succ y) = 
        x + succ y
            ＝⟨ refl _ ⟩ 
        succ (x + y)
            ＝⟨ ap succ (+-conmutative x y) ⟩ 
        succ (y + x) 
            ＝⟨ succ+y y x ⁻¹ ⟩ 
        succ y + x
        ∎
    

    succ*y : (x y : ℕ) → succ x ⋆ y ＝ x ⋆ y + y 
    succ*y x zero = refl zero
    succ*y x (succ y) = succ+y x (succ x ⋆ y) ∙ (ap (λ t → succ (x + t)) (succ*y x y)) ∙ (ap succ (+-assoc x (x ⋆ y) y ⁻¹))

-- Propiedades de orden

data Bool : 𝓤₀ ̇   where
    true : Bool 
    false : Bool


_≤_ : ℕ → ℕ → Bool
n ≤ m = ?

    
-- _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
-- 0      ≤ y      = 𝟙
-- succ x ≤ 0      = 𝟘
-- succ x ≤ succ y = x ≤ y

-- x ≥ y = y ≤ x

-- infix 10 _≤_
-- infix 10 _≥_

-- one-is-gt-zero : ¬ (1 ≤ 0)
-- one-is-gt-zero = !𝟘 𝟘

-- succ-is-gt-num : (x : ℕ) → ¬ (succ x ≤ x)
-- succ-is-gt-num zero = one-is-gt-zero
-- succ-is-gt-num (succ x) = succ-is-gt-num x

-- ≤-injective : {x y : ℕ} → (z : ℕ) → x + z ≤ y + z → x ≤ y
-- ≤-injective {x} {y} zero ind = ind
-- ≤-injective {x} {y} (succ z) ind = ≤-injective z ind

-- ≤-reflexive : (x : ℕ) → x ≤ x
-- ≤-reflexive zero = *
-- ≤-reflexive (succ x) = ≤-reflexive x

-- ≤-transitive-aux : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
-- ≤-transitive-aux zero y z x≤y y≤z = *
-- ≤-transitive-aux (succ x) zero z x≤y y≤z = !𝟘 _ x≤y
-- ≤-transitive-aux (succ x) (succ y) zero x≤y y≤z = !𝟘 _ y≤z
-- ≤-transitive-aux (succ x) (succ y) (succ z) x≤y y≤z = ≤-transitive-aux x y z x≤y y≤z

-- ≤-transitive : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
-- ≤-transitive {x} {y} {z} = ≤-transitive-aux x y z

-- ≤-succ : (x : ℕ) → x ≤ succ x
-- ≤-succ zero = *
-- ≤-succ (succ x) = ≤-succ x

-- ≤-dec : (x y : ℕ) → decidable (x ≤ y) 
-- ≤-dec zero zero = inl *
-- ≤-dec zero (succ y) = inl *
-- ≤-dec (succ x) zero = inr id
-- ≤-dec (succ x) (succ y) = ≤-dec x y

-- -- 
-- _<_  : ℕ → ℕ → 𝓤₀ ̇ 
-- 0      < 0      = 𝟘
-- 0      < succ y = 𝟙
-- succ x < 0      = 𝟘
-- succ x < succ y = x < y

-- -- 

-- max : ℕ → ℕ → ℕ 
-- max  0        y       = y
-- max (succ x)  0       = succ x
-- max (succ x) (succ y) = succ (max x y)

-- _∸_ : ℕ → ℕ → ℕ 
-- 0      ∸ y      = 0
-- succ x ∸ 0      = succ x
-- succ x ∸ succ y = x ∸ y  
-- infixl 20 _∸_

-- max-refl : (x y : ℕ) → max x y ＝ max y x 
-- max-refl  0        0       = refl 0
-- max-refl  0       (succ y) = refl (succ y)
-- max-refl (succ x)  0       = refl (succ x)
-- max-refl (succ x) (succ y) = ap succ (max-refl x y)

-- max-assoc : (x y z : ℕ) → max (max x y) z ＝ max x (max y z)
-- max-assoc 0         y        z       = refl _
-- max-assoc (succ x)  0        z       = refl _
-- max-assoc (succ x) (succ y)  0       = refl _
-- max-assoc (succ x) (succ y) (succ z) = ap succ (max-assoc x y z)

-- x≤max : (x y : ℕ) → x ≤ max x y 
-- x≤max  0        y       = *
-- x≤max (succ x)  0       = ≤-reflexive x
-- x≤max (succ x) (succ y) = x≤max x y

-- y≤max : (x y : ℕ) → y ≤ max x y 
-- y≤max  x y = transport (y ≤_) (max-refl y x) (x≤max y x)

-- z≤x-then-z≤max-x-y : (x y z : ℕ) → z ≤ x → z ≤ max x y 
-- z≤x-then-z≤max-x-y  _ _               0       z≤x = *
-- z≤x-then-z≤max-x-y  0       y        (succ z) z≤x = !𝟘 _ z≤x
-- z≤x-then-z≤max-x-y (succ x) 0        (succ z) z≤x = z≤x
-- z≤x-then-z≤max-x-y (succ x) (succ y) (succ z) z≤x = z≤x-then-z≤max-x-y x y z z≤x

-- z≤y-then-z≤max-x-y : (x y z : ℕ) → z ≤ y → z ≤ max x y 
-- z≤y-then-z≤max-x-y x y z z≤y = transport (z ≤_) (max-refl y x) (z≤x-then-z≤max-x-y y x z z≤y)

-- y≤z-then-max-x-y≤max-x-z : (x y z : ℕ) → y ≤ z → max x y ≤ max x z 
-- y≤z-then-max-x-y≤max-x-z  x        0        0       y≤z = ≤-reflexive (max x 0)
-- y≤z-then-max-x-y≤max-x-z  0        0       (succ y) y≤z = *
-- y≤z-then-max-x-y≤max-x-z (succ x)  0       (succ y) y≤z = x≤max x y
-- y≤z-then-max-x-y≤max-x-z  0       (succ y) (succ z) y≤z = y≤z
-- y≤z-then-max-x-y≤max-x-z (succ x) (succ y) (succ z) y≤z = y≤z-then-max-x-y≤max-x-z x y z y≤z

-- ≤-gets-diff : (y z : ℕ) → (y ≤ z) → Σ x ꞉ ℕ , x + y ＝ z 
-- ≤-gets-diff  0        z       y≤z = z , refl z
-- ≤-gets-diff (succ y)  0       y≤z = !𝟘 _ y≤z
-- ≤-gets-diff (succ y) (succ z) y≤z = pr₁ r,q , ap succ (pr₂ r,q)
--     where 
--     r,q = ≤-gets-diff y z y≤z

-- diff-gets-max : (x y : ℕ) → x + (y ∸ x) ＝ max x y  
-- diff-gets-max  0        0       = refl 0
-- diff-gets-max  0       (succ y) = ap succ (Peano.zero+n y)
-- diff-gets-max (succ x)  0       = refl _
-- diff-gets-max (succ x) (succ y) = Peano.succ+y x (y ∸ x) ∙ (ap succ (diff-gets-max x y))

-- max-x-zero-is-x : (x : ℕ) → max x 0 ＝ x
-- max-x-zero-is-x  0       = refl 0
-- max-x-zero-is-x (succ x) = refl (succ x)

-- x∸≤-is-zero : (x y : ℕ) → (x ≤ y) → x ∸ y ＝ 0
-- x∸≤-is-zero  0        0       p = refl 0
-- x∸≤-is-zero  0       (succ y) p = refl 0
-- x∸≤-is-zero (succ x)  0       p = !𝟘 _ p
-- x∸≤-is-zero (succ x) (succ y) p = x∸≤-is-zero x y p