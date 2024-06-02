-- {-# OPTIONS --without-K --exact-split --safe --auto-inline #-}
-- sin safe no se puede postular univalencia
-- --cubical para HIT
{-# OPTIONS --without-K --exact-split --auto-inline #-}
module MLTT where

open import Raise public
open import Universes public

variable 𝓤 𝓥 𝓦 𝓣 : Universe 

-- 
-- 1. El tipo con un elemento: 𝟙
-- 

-- Definición à la MLTT
-- data 𝟙 : 𝓤₀ ̇  where
--     * : 𝟙

-- Definición para que Agda entienda el tipo como tipo básico
record 𝟙 : 𝓤₀ ̇  where 
    instance constructor * 
{-# BUILTIN UNIT 𝟙 #-}

𝟙-induction : (A : 𝟙 → 𝓤 ̇ ) → A * → (x : 𝟙) → A x
𝟙-induction A a * = a

𝟙-recursion : (B : 𝓤 ̇ ) → B → 𝟙 → B
𝟙-recursion B b * = 𝟙-induction (λ _ → B) b *

!𝟙 : {X : 𝓤 ̇ } → X → 𝟙
!𝟙 _ = *

-- 
-- 2. EL tipo vacío: 𝟘
--
data 𝟘 : 𝓤₀ ̇  where

𝟘-induction : (A : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A
𝟘-recursion A x = 𝟘-induction (λ _ → A) x

!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇  → 𝓤 ̇ 
is-empty X = X → 𝟘

¬ : 𝓤 ̇  → 𝓤 ̇  
¬ = is-empty


-- 
-- 3. Los números naturales ℕ
-- 

data ℕ : 𝓤₀ ̇  where 
    zero : ℕ
    succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ → 𝓤 ̇ )
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction A a₀ ind zero = a₀
ℕ-induction A a₀ ind (succ n) = ind n (ℕ-induction A a₀ ind n)

ℕ-recursion : (X : 𝓤 ̇ )
            → X
            → (ℕ → X → X)
            → ℕ → X 
ℕ-recursion X x rec n = ℕ-induction (λ _ → X) x rec n

ℕ-iteration : (X : 𝓤 ̇ )
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

-- 
-- 4. La suma binaria / suma disjunta +
-- 

data _+_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
    inl : X → X + Y
    inr : Y → X + Y

infixr 20 _+_

+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ )
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → (z : X + Y) → A z

+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-recursion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → (X → A) → (Y → A) → X + Y → A
+-recursion {𝓤} {𝓥} {𝓦} {X} {Y} {A} = +-induction (λ _ → A)

-- El tipo con dos puntos
𝟚 : 𝓤₀ ̇ 
𝟚 = 𝟙 + 𝟙

-- pattern ₀ = inl *
-- pattern ₁ = inr *

-- 𝟚-induction : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
-- 𝟚-induction A a₀ a₁ ₀ = a₀
-- 𝟚-induction A a₀ a₁ ₁ = a₁

-- 
-- 5. Suma dependiente Σ 
-- 

record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
    constructor
        _,_
    field
        x : X
        y : Y x

infixr 50 _,_

Σ' : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
Σ' X = Σ {_} {_} {X}
{-# BUILTIN SIGMA Σ' #-}

pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

-- Sintáxis para escribir Σ x : X, Y en vez de Σ λ(x : X) → Y
-- IMPORTANTE: El símbolo ꞉ usado aquí es en realidad \:4
-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ꞉ X , y

infixr -1 -Σ

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) → (y : Y x) → A (x , y))
            → (z : Σ Y) → A z
Σ-induction f (x , y) = f x y

-- Como caso particular, tenemos el tipo producto ×
_×_ : 𝓤 ̇  → 𝓥 ̇  → 𝓤 ⊔ 𝓥 ̇ 
X × Y = Σ  x ꞉ X , Y

infixr 30 _×_

-- 
-- 6. Tipo producto Π
-- 

-- IMPORTANTE: El símbolo ꞉ usado aquí es en realidad \:4
Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ꞉ A , b

id : {X : 𝓤 ̇ } → X → X
id x = x

-- Mii Mid (i.e. Mathematical italics)
𝑖𝑑 : (X : 𝓤 ̇ ) → X → X
𝑖𝑑 _ x = x -- 𝑖𝑑 X = id

_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)

infixl 70 _∘_

domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇ 
domain {𝓤} {𝓥} {X} f = X 

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇ 
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇ 
type-of {𝓤} {X} x = X

-- 
-- 7. Razonando con negación
-- 

¬¬ ¬¬¬ : 𝓤 ̇  → 𝓤 ̇ 
¬¬ A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)

-- double negation introduction
dni : (A : 𝓤 ̇ ) → A → ¬¬ A
dni A a u = u a

contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (¬ B → ¬ A)
contrapositive f notb a = notb (f a)

-- triple negation imply one
tno : (A : 𝓤 ̇ ) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)

-- \lr-- ⟷
_⟷_ : 𝓤 ̇  → 𝓥 ̇  → 𝓤 ⊔ 𝓥 ̇ 
X ⟷ Y = (X → Y) × (Y → X)

infix  10 _⟷_

lr-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⟷ Y) → (X → Y)
lr-implication = pr₁

rl-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⟷ Y) → (Y → X)
rl-implication = pr₂

-- 
-- 8. El tipo identidad ＝
--

data _＝_ {X : 𝓤 ̇ } : X → X → 𝓤 ̇  where
    refl : (x : _) → x ＝ x
{-# BUILTIN EQUALITY _＝_  #-}

infix   0 _＝_

𝕁 : (X : 𝓤 ̇ ) (A : (x y : X) → x ＝ y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ＝ y) → A x y p
𝕁 X A f x x (refl x) = f x

transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ＝ y → A x → A y
transport A (refl x) = 𝑖𝑑 (A x)

transport𝕁 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ＝ y → A x → A y
transport𝕁 {𝓤} {𝓥} {X} A {x} {y} = 𝕁 X (λ x y _ → A x → A y) (λ x → 𝑖𝑑 (A x)) x y

lhs : {X : 𝓤 ̇ } {x y : X} → x ＝ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ＝ y → X
rhs {𝓤} {X} {x} {y} p = y

-- Se escribe \. 
_∙_ : {X : 𝓤 ̇ } {x y z : X} → (x ＝ y) → (y ＝ z) → (x ＝ z)
p ∙ q = transport (lhs p ＝_) q p

-- Estamos considerando la famila x = -
-- Como tenemos y = z, y la igualdad x = y,
-- que es un elemento de la familia, transport lleva la 
-- el elemento x = y por la igualdad y = z al elemento x = z, fin

infixl 30 _∙_

-- Otra forma, como viene dado en el libro
_∙'_ : {X : 𝓤 ̇ } {x y z : X} → (x ＝ y) → (y ＝ z) → (x ＝ z)
_∙'_ {𝓤} {X} {x} {y} {z} p q = f y p z q where
      f : {X : 𝓤 ̇ } {x : X} → (y : X) → (x ＝ y) → (z : X) → (y ＝ z) → (x ＝ z)
      f y (refl .y) z q = q

_＝⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ＝ y → y ＝ z → x ＝ z
x ＝⟨ p ⟩ q = p ∙ q

infixr  0 _＝⟨_⟩_

_∎ : {X : 𝓤 ̇ } (x : X) → x ＝ x
x ∎ = refl x

infix   1 _∎

_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ＝ y → y ＝ x
p ⁻¹ = transport (_＝ lhs p) p (refl (lhs p))
infix  40 _⁻¹
-- Tomamos el tipo - = x. Tenemos la igualdad x = y,
-- y el elemento x = x. Transportando, obtenemos el 
-- elemento y = x.

refl-right : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y)
      → p ∙ refl y ＝ p
refl-right (refl _) = refl _

refl-left : {X : 𝓤 ̇ } {y z : X} (q : y ＝ z)
      → refl y  ∙ q ＝ q

refl-left (refl _) = refl _

∙assoc : {X : 𝓤 ̇ } {x y z t : X} (p : x ＝ y) (q : y ＝ z) (r : z ＝ t)
       → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙assoc p q (refl _) = refl (p ∙ q)

⁻¹-left∙ : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y)
             → p ⁻¹ ∙ p ＝ refl y
⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-right∙ : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y)
          → p ∙ p ⁻¹ ＝ refl x
⁻¹-right∙ (refl x) = refl (refl x)

ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ＝ x' → f x ＝ f x'
ap f {x} {x'} p = transport (λ - → f x ＝ f -) p (refl (f x))
-- Consideramos el tipo f x = f -
-- Tenemos la igualdad x = x'
-- Podemos construir el elemento f x = f x (por reflexividad)
-- Transportando, fin

ap-id : {X : 𝓤 ̇ } {x x' : X} → (p : x ＝ x') → ap id p ＝ p
ap-id (refl _) = refl _

-- Razonando con no igualdades

_≠_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≠ y = ¬(x ＝ y)

≠-sym : {X : 𝓤 ̇ } {x y : X} → x ≠ y → y ≠ x
≠-sym {𝓤} {X} {x} {y} u = λ (p : y ＝ x) → u (p ⁻¹)
-- Tenemos u : x = y → 𝟘, y queremos y = x → 𝟘
-- Para construir esta función, dado un p : y = x,
-- lo invertimos y obtenemos un p ⁻¹ : x = y,
-- el cual aplicando u se obtiene u (p ⁻¹) : 𝟘


Id→Fun : {X Y : 𝓤 ̇ } → X ＝ Y → X → Y
Id→Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇ ))
𝟙-is-not-𝟘 : 𝟙 ≠ 𝟘
𝟙-is-not-𝟘 p = Id→Fun p *

-- ₁-is-not-₀ : ₁ ≠ ₀
-- ₁-is-not-₀ p = 𝟙-is-not-𝟘 q 
--   where
--     f : 𝟚 → 𝓤₀ ̇ 
--     f ₀ = 𝟘
--     f ₁ = 𝟙

--     q : 𝟙 ＝ 𝟘
--     q = ap f p

-- Decibilidad

decidable : 𝓤 ̇  → 𝓤 ̇ 
decidable A = A + ¬ A

has-decidable-equality : 𝓤 ̇  → 𝓤 ̇ 
has-decidable-equality X = (x y : X) → decidable (x ＝ y)

-- 𝟚-has-decidable-equality : has-decidable-equality 𝟚
-- 𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
-- 𝟚-has-decidable-equality ₀ ₁ = inr (≠-sym ₁-is-not-₀)
-- 𝟚-has-decidable-equality ₁ ₀ = inr (₁-is-not-₀)
-- 𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)

-- not-zero-is-one : (n : 𝟚) → n ≠ ₀ → n ＝ ₁
-- not-zero-is-one ₀ f = !𝟘 (₀ ＝ ₁) (f (refl ₀))
-- not-zero-is-one ₁ f = refl ₁

Eqℕ : ℕ → ℕ → 𝓤₀ ̇ 
Eqℕ zero zero = 𝟙
Eqℕ zero (succ y) = 𝟘
Eqℕ (succ x) zero = 𝟘
Eqℕ (succ x) (succ y) = Eqℕ x y

Eqℕ-refl : (n : ℕ) → Eqℕ n n 
Eqℕ-refl zero = *
Eqℕ-refl (succ n) = Eqℕ-refl n

Eqℕ-equiv-Id : (m n : ℕ) → ((m ＝ n) ⟷ Eqℕ m n)
Eqℕ-equiv-Id m n = ((first-implication m n) , (second-implication m n)) 
  where
    first-implication : (m n : ℕ) → (m ＝ n) → Eqℕ m n
    first-implication m m (refl m) = Eqℕ-refl m

    second-implication : (m n : ℕ) → Eqℕ m n → (m ＝ n)
    second-implication zero zero p = refl 0
    second-implication zero (succ n) p = !𝟘 (0 ＝ (succ n)) p
    second-implication (succ m) zero p = !𝟘 ((succ m) ＝ 0) p
    second-implication (succ m) (succ n) p = ap succ (second-implication m n p)
    -- En este último caso, por inducción construimos m = n, y aplicando succ,
    -- conseguimos succ n = succ m

Eqℕ-is-decidable : (m n : ℕ) → decidable (Eqℕ m n)
Eqℕ-is-decidable zero zero = inl *
Eqℕ-is-decidable zero (succ n) = inr (𝑖𝑑 𝟘)
Eqℕ-is-decidable (succ m) zero = inr (𝑖𝑑 𝟘)
Eqℕ-is-decidable (succ m) (succ n) = Eqℕ-is-decidable m n

decidable-iff-decidable : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A ⟷ B) → (decidable A ⟷ decidable B)
decidable-iff-decidable {A} {B} equiv = (f equiv , g equiv)
  where
    f : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A ⟷ B) → decidable A → decidable B 
    f equiv (inl x) = inl (lr-implication equiv x)
    f equiv (inr y) = inr (λ x → y (pr₂ equiv x))
    g : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A ⟷ B) → decidable B → decidable A
    g equiv decidB = f (rl-implication equiv , lr-implication equiv) decidB 

ℕ-has-decidable-equality : has-decidable-equality ℕ
ℕ-has-decidable-equality m n = rl-implication (decidable-iff-decidable (Eqℕ-equiv-Id m n)) 
                                    (Eqℕ-is-decidable m n)


 
-- 
-- 9. Homotopía
-- 
-- \sim

_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ∼ g = (x : _) → f x ＝ g x
infix   0 _∼_


relf-htpy : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → (f : Π A) → (f ∼ f)
relf-htpy f = λ x → refl (f x)

inv-htpy : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → (f ∼ g) → (g ∼ f)
inv-htpy H = λ x → (H x)⁻¹

concat-htpy : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → {f g h : Π A}
            → (f ∼ g) → (g ∼ h) → (f ∼ h)
concat-htpy H K = λ x → (H x) ∙ (K x)

assoc-htpy : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g h i : Π A}
           → (H : f ∼ g) → (K : g ∼ h) → (L : h ∼ i)
           → (concat-htpy (concat-htpy H  K) L ∼ concat-htpy H (concat-htpy K L))
assoc-htpy H K L = λ x → ∙assoc (H x) (K x) (L x)

left-unit-htpy : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} 
                 → (H : f ∼ g) → concat-htpy (relf-htpy f) H ∼ H
left-unit-htpy {𝓤} {𝓥} {X} {A} {f} H = λ x → refl-left (H x)

right-unit-htpy : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} 
                 → (H : f ∼ g) → H ∼ concat-htpy H (relf-htpy g) 
right-unit-htpy {𝓤} {𝓥} {X} {A} {f} {g} H = λ x → refl-right (H x)

-- left-inv-htpy : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} 
--               → (H : f ∼ g) → concat-htpy (inv-htpy H) H ∼ (relf-htpy g)
-- left-inv-htpy H = λ x → 

-- Whiskering 
left-W : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f g : X → Y} (h : Y → Z) (H : f ∼ g) 
       → h ∘ f ∼ h ∘ g
left-W {_} {_} {_} {_} {_} {_} {f} {g} h H = λ x → ap h (H x)

right-W : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {g h : Y → Z} (H : g ∼ h) (f : X → Y)
       → g ∘ f ∼ h ∘ f
right-W {_} {_} {_} {_} {_} {_} {g} {h} H f = λ x → H (f x) -- otra cosa mal 

has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇ 
has-section r = Σ s ꞉ (codomain r → domain r) , r ∘ s ∼ id

has-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇ 
has-retraction r = Σ s ꞉ (codomain r → domain r) , s ∘ r ∼ id

-- ⦉ 
_◁_ : 𝓤 ̇  → 𝓥 ̇  → 𝓤 ⊔ 𝓥 ̇
X ◁ Y = Σ r ꞉ (Y → X) , has-section r
infix  10 _◁_

retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → Y → X
retraction (r , s , η) = r

section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → X → Y
section (r , s , η) = s

retraction-is-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (ρ : X ◁ Y) 
                         → has-retraction (section ρ)
retraction-is-retraction (r , s , μ) = (r , μ)

id-◁ : (X : 𝓤 ̇ ) → X ◁ X
id-◁ X = 𝑖𝑑 X , 𝑖𝑑 X , refl

_◁∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z

(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , η'')
 where
  η'' = λ x → r (r' (s' (s x))) ＝⟨ ap r (η' (s x)) ⟩
              r (s x)           ＝⟨ η x             ⟩
              x                 ∎

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ
infixr  0 _◁⟨_⟩_

_◀ : (X : 𝓤 ̇ ) → X ◁ X
X ◀ = id-◁ X
infix   1 _◀

is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇ 
is-equiv f = (has-section f) × (has-retraction f)

-- ­\simeq
_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ f ꞉ (X → Y), is-equiv f
infix  10 _≃_

≃-refl : (X : 𝓤 ̇ ) → X ≃ X
≃-refl X = id , ((id , refl) , id , refl)

id-is-equiv : {X : 𝓤 ̇ } → is-equiv (𝑖𝑑 X)
id-is-equiv {X} = ((id , refl) , (id , refl))

has-inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇ 
has-inverse f = Σ g ꞉ (codomain f → domain f), (f ∘ g ∼ id) × (g ∘ f ∼ id)

invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇ 
invertible f = Σ g ꞉ (codomain f → domain f), (g ∘ f ∼ id) × (f ∘ g ∼ id)

has-inverse-equiv-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y)
    → has-inverse f ≃ invertible f 
has-inverse-equiv-invertible f = has-inverse-invertible , (invertible-has-inverse , lemma-1) , invertible-has-inverse , lemma-2 where
    has-inverse-invertible : has-inverse f → invertible f
    has-inverse-invertible (g , (h₁ , h₂)) = g , (h₂ , h₁)

    invertible-has-inverse : invertible f → has-inverse f 
    invertible-has-inverse (g , (h₁ , h₂)) = g , (h₂ , h₁)

    lemma-1 : (x : _) → has-inverse-invertible (invertible-has-inverse x) ＝ x
    lemma-1 (g , h₁ , h₂) = refl (g , h₁ , h₂)

    lemma-2 : (x : _) → invertible-has-inverse (has-inverse-invertible x) ＝ x
    lemma-2 (g , h₁ , h₂) = refl (g , h₁ , h₂) 


has-inverse-is-equivalence : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) 
                           → has-inverse f → is-equiv f 
has-inverse-is-equivalence f (g , H , G) = (g , H) , (g , G)

is-equiv-has-inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) 
                           → is-equiv f → has-inverse f
is-equiv-has-inverse f ((h , H) , (g , G)) = g , (L , G) where
    K : g ∼ h
    K = λ y → g y         ＝⟨ ap g ((H y) ⁻¹) ⟩
              g (f (h y)) ＝⟨ G (h y)         ⟩ 
              h y         ∎

    L : f ∘ g ∼ id
    L = λ y → f (g y) ＝⟨ ap f (K y) ⟩ 
              f (h y) ＝⟨ H y ⟩ 
              y       ∎

invertible-is-equivalence : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) 
                           → invertible f → is-equiv f
invertible-is-equivalence f = (has-inverse-is-equivalence f) ∘ (pr₁ (pr₂ (pr₂ (has-inverse-equiv-invertible f))))

≃-sim : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → Y ≃ X
≃-sim (f , f-equiv) = g , (f , (pr₂ htpy)) , (f , (pr₁ htpy)) where
    g : codomain f → domain f
    g = pr₁ (is-equiv-has-inverse f f-equiv)

    htpy : (f ∘ g ∼ id) × (g ∘ f ∼ id) 
    htpy = pr₂ (is-equiv-has-inverse f f-equiv)

-- inverse-of-equiv-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) 
--                           → (((s , _) , _) : is-equiv f)
--                           → is-equiv s
-- inverse-of-equiv-is-equiv f ((s , _) , _) = 

+-left-unit-equivalence : (B : 𝓤 ̇ ) → 𝟘 + B ≃ B
+-left-unit-equivalence B = (f , isequiv ) where
    f : 𝟘 + B → B
    f (inl x) = !𝟘 B x
    f (inr y) = y

    g : (z : 𝟘 + B) → inr (f z) ＝ z
    g (inl x) = !𝟘 _ x
    g (inr y) = refl (inr y)

    isequiv : is-equiv f
    isequiv = (inr , refl) , (inr , g)

+-commutes-equivalence : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A + B ≃ B + A
+-commutes-equivalence {𝓤} {𝓥} {A} {B} = (f A B) , isequiv  where

    f : {𝓤 𝓥 : Universe} → (A : 𝓤 ̇ ) → (B : 𝓥 ̇ ) → A + B → B + A
    f A B (inl x) = inr x
    f A B (inr x) = inl x

    f-inverses : {𝓤 𝓥 : Universe} → (A : 𝓤 ̇ ) → (B : 𝓥 ̇ )
               → (f A B) ∘ (f B A) ∼ id
    f-inverses A B (inl x) = refl (inl x)
    f-inverses A B (inr x) = refl (inr x) 
    
    isequiv : is-equiv (f A B)
    isequiv = ((f B A) , f-inverses A B) , ((f B A) , f-inverses B A)

-- etc.


-- Caracterización de los tipo identidad para los tipos Σ 

EqΣ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ }
    → Σ B → Σ B → 𝓤 ⊔ 𝓥 ̇ 
EqΣ {_} {_} {_} {B} (x , y) (z , w) = Σ α ꞉ (x ＝ z) , ((transport B α y) ＝ w)

reflexive-EqΣ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → (s : Σ B) → EqΣ s s
reflexive-EqΣ (x , y) = (refl x) , (refl y)

pair-eq : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → (s t : Σ B)
        → (s ＝ t) → EqΣ s t
pair-eq s s (refl s) = reflexive-EqΣ s

pair-eq-is-equiv : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → (s t : Σ B)
                 → is-equiv (pair-eq s t)
pair-eq-is-equiv s t = (eq-pair s t , pair-eq-eq-pair) , (eq-pair s t , eq-pair-pair-eq) where

    eq-pair : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → (s t : Σ B)
        → EqΣ s t → (s ＝ t)
    eq-pair (x , y) (x , y) (refl x , refl y) = refl (x , y)

    pair-eq-eq-pair : (pair-eq s t) ∘ (eq-pair s t) ∼ id
    pair-eq-eq-pair (refl .(pr₁ s) , refl .(pr₂ t)) = refl (refl (pr₁ s) , refl (pr₂ t))

    eq-pair-pair-eq : (eq-pair s t) ∘ (pair-eq s t) ∼ id
    eq-pair-pair-eq (refl (x , y)) = refl (refl (x , y))

--
-- 10. Tipos contráctiles / unitarios
-- 

is-singleton : 𝓤 ̇  → 𝓤 ̇ 
is-singleton X = Σ c ꞉ X , ((x : X) → c ＝ x)

is-center : (X : 𝓤 ̇ ) → X → 𝓤 ̇
is-center X c = (x : X) → c ＝ x

is-center-implies-is-singleton : (X : 𝓤 ̇ ) → (c : X) → (is-center X c) 
    → (is-singleton X)
is-center-implies-is-singleton X c p = c , p

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = * , 𝟙-induction ((λ x → * ＝ x)) (refl *)

center : (X : 𝓤 ̇ ) → is-singleton X → X
center X (c , φ) = c

centrality : (X : 𝓤 ̇ ) (i : is-singleton X) (x : X) → center X i ＝ x
centrality X (c , φ) = φ

constant-at-c : {X : 𝓤 ̇ } (c : X) → (X → X)
constant-at-c c = λ x → c

costant-at-center-is-htpy-to-id : (X : 𝓤 ̇ ) → (p : is-singleton X)
                                → (constant-at-c (center X p) ∼ id)
costant-at-center-is-htpy-to-id X p = centrality X p

--
-- Singleton induction
--

ev-pt : (A : 𝓤 ̇ ) → (B : A → 𝓥 ̇ ) → (a : A) → (Π B → B a)
ev-pt A b a f = f a

singleton-induction : (A : 𝓤 ̇ ) (a : A)
                    → (B : A → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇ 
singleton-induction A a = λ B → has-section (ev-pt A B a)

singleton-induction-ind-sing : (A : 𝓤 ̇ ) → (a : A) → (B : A → 𝓥 ̇ )
    → (singleton-induction A a B)
    → (B a → Π B)
singleton-induction-ind-sing A a B (f , _) = f
 
singleton-iff-singleton-induction : (A : 𝓤 ̇ ) →
    (is-singleton A) ⟷ (Σ a ꞉ A , ((B : _) → (singleton-induction A a B)))
singleton-iff-singleton-induction A = p1 , p2 where

    p1 : is-singleton A → (Σ a ꞉ A , ((B : _) → singleton-induction A a B))
    p1 (a , C) = a , λ B → ind-sing B , ind-sing-htpy B where

        C' : (x : A) → a ＝ x
        C' x = (C a)⁻¹ ∙ (C x)

        p : (C' a) ＝ (refl a)
        p = ⁻¹-left∙ (C a)

        ind-sing : (B : _) → B a → Π B
        ind-sing B b = λ x → transport B (C' x) b

        ind-sing-htpy : (B : _) →  (λ b → ind-sing B b a) ∼ id
        ind-sing-htpy B = λ b → ind-sing B b a         ＝⟨ ap (λ ω → transport B ω b) p ⟩
                                transport B (refl a) b ＝⟨ refl b ⟩ 
                                b                      ∎

    p2 : (Σ a ꞉ A , ((B : _) → singleton-induction A a B)) → is-singleton A
    p2 (a , sing-ind) = a , singleton-induction-ind-sing A a (λ x → a ＝ x) (sing-ind (λ x → a ＝ x)) (refl a) 


--
-- Aplicaciones contráctiles
--


-- fibra de f en y
fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ x ꞉ domain f , f x ＝ y

fiber-point : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y}
            → fiber f y → X
fiber-point (x , p) = x


fiber-identification : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y}
                     → (w : fiber f y) → f (fiber-point w) ＝ y
fiber-identification (x , p) = p

Eq-fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y} (z w : fiber f y)
         → 𝓤 ⊔ 𝓥 ̇ 
Eq-fiber {𝓤} {𝓥} {X} {Y} {f} (x , p) (x' , p') = Σ α ꞉ (x ＝ x') , (p ＝ (ap f α) ∙ p')

Eq-fiber-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y} (z : fiber f y)
              → Eq-fiber z z
Eq-fiber-refl {𝓤} {𝓥} {X} {Y} {f} {y} (x , p) = (refl x) , ((refl-left p)⁻¹)

Id-to-eq-fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (y : Y) 
               → (z w : fiber f y) → ((z ＝ w) → Eq-fiber z w)
Id-to-eq-fiber f y z z (refl z) = Eq-fiber-refl z

Id-to-eq-fiber-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (y : Y) (z w : fiber f y)
                        → is-equiv (Id-to-eq-fiber f y z w)
Id-to-eq-fiber-is-equiv f y z w = (Id-to-eq-fiber-inverse f y z w , H z w) , 
                                (Id-to-eq-fiber-inverse f y z w , G z w) where
    Id-to-eq-fiber-inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (y : Y) 
                           → (z w : fiber f y) →  Eq-fiber z w → z ＝ w
    Id-to-eq-fiber-inverse f y (x , _) (x , refl y) (refl x , refl _) = refl (x , refl y)

    H : (z w : fiber f y) → (λ x → Id-to-eq-fiber f y z w (Id-to-eq-fiber-inverse f y z w x)) ∼ id
    H (x , _) (x , refl y) (refl x , refl _) = refl (refl x , refl (refl y))

    G : (z w : fiber f y) → (λ x → Id-to-eq-fiber-inverse f y z w (Id-to-eq-fiber f y z w x)) ∼ id
    G (x , refl y) (x , (refl y)) (refl (x , refl y)) = refl (refl (x , refl y))


is-contr : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇ 
is-contr f = Π y ꞉ (codomain f) , is-singleton (fiber f y)

is-contr-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) → is-contr f → is-equiv f
is-contr-is-equiv {𝓤} {𝓥} {X} {Y} f iscontrf = (g , G) , (g , H) where

    F : (y : Y) → fiber f y 
    F y = center (fiber f y) (iscontrf y)

    g : Y → X
    g y = fiber-point (F y)

    G : (λ y → f (g y)) ∼ id
    G y = fiber-identification (F y)

    H : (x : _) → g (f x) ＝ x
    H x = ap pr₁ q where

        p : f (g (f x)) ＝ f x
        p = (G (f x))

        c : fiber f (f x)
        c = center (fiber f (f x)) (iscontrf (f x))

        C : (z : fiber f (f x)) → c ＝ z
        C z = centrality (fiber f (f x)) (iscontrf (f x)) z

        q1 : c ＝ (g (f x) , p)
        q1 = C (g (f x) , p)

        q2 : c ＝ (x , refl (f x))
        q2 = C (x , refl (f x))    

        q : (g (f x) , p) ＝ (x , refl (f x))
        q  = q1 ⁻¹ ∙ q2

is-coherently-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) → 𝓤 ⊔ 𝓥 ̇ 
is-coherently-invertible {𝓤} {𝓥} {X} {Y} f = 
    Σ g ꞉ (Y → X) , 
    Σ G ꞉ (f ∘ g ∼ id) , 
    Σ H ꞉ (g ∘ f ∼ id) , 
    (right-W G f) ∼ (left-W f H)

coherently-invertible-has-contractible-fibers : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) 
    → is-coherently-invertible f 
    → (y : _) → is-singleton (fiber f y)
coherently-invertible-has-contractible-fibers f (g , G , H , K) y 
    = ((g y , G y)) , L where
    
    F : (x : _) (p : (f x) ＝ y) → (Eq-fiber (g y , G y) (x , p))
    F x (refl y) = (H x) , (concat-htpy K (inv-htpy (right-unit-htpy (left-W f H)))) x

    L : (z : fiber f y) → g y , G y ＝ z
    L (x , p) = aux (F x p) where

        z w : fiber f y
        z = (g y , G y)
        w = (x , p)

        aux : Eq-fiber z w → z ＝ w
        aux eq = pr₁ (pr₁ (Id-to-eq-fiber-is-equiv f y z w)) eq

nat-htpy : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x y : X} {f g : X → Y}
    (H : f ∼ g) (p : x ＝ y)
    → (ap f p) ∙ (H y) ＝ (H x) ∙ (ap g p)
nat-htpy {_} {_} {_} {_} {x} {_} {f} {g} H (refl x) = 
    ap f (refl x) ∙ H x ＝⟨ refl-left (H x) ⟩ 
    H x                 ＝⟨ (refl-right (H x))⁻¹ ⟩
    H x ∙ ap g (refl x) ∎

nat-id-htpy : {X : 𝓤 ̇ } 
    → (f : X → X) → (H : f ∼ id) 
    → (x : X) → H (f x) ＝ ap f (H x)
nat-id-htpy f H x = 
    H (f x)                     ＝⟨ aux (H (f x)) (H x) ⟩ 
    H (f x) ∙ H x ∙ (H x)⁻¹     ＝⟨ ap (_∙ (H x)⁻¹) (nat ⁻¹) ⟩ 
    ap f (H x) ∙ H x ∙ (H x)⁻¹  ＝⟨ (aux (ap f (H x)) (H x))⁻¹ ⟩ 
    ap f (H x)                  ∎ where

    aux : {X : 𝓤 ̇ } {x y z : X} 
        → (p : x ＝ y) (q : y ＝ z) 
        → p ＝ (p ∙ q) ∙ q ⁻¹
    aux (refl _) (refl _) = refl _

    nat : ap f (H x) ∙ H x ＝ H (f x) ∙ H x
    nat =   ap f (H x) ∙ H x       ＝⟨ nat-htpy H (H x) ⟩ 
            H (f x) ∙ ap id (H x)  ＝⟨ ap (H (f x) ∙_) (ap-id (H x)) ⟩ 
            H (f x) ∙ H x          ∎

 
has-inverse-is-coh-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y)
    → has-inverse f → is-coherently-invertible f
has-inverse-is-coh-invertible f (g , G , H) = g , G' , H , K where

    G' : f ∘ g ∼ id
    G' = λ y → (G (f (g y))) ⁻¹ ∙ ap f (H (g y)) ∙ G y 

    K : (right-W G' f ) ∼ (left-W f H)
    K x = right-W G' f x ＝⟨ refl _ ⟩ 
            (G (f (g (f x)))) ⁻¹ ∙ ap f (H (g (f x))) ∙ G (f x)   ＝⟨ ∙assoc ((G (f (g (f x)))) ⁻¹) (ap f (H (g (f x)))) (G (f x)) ⟩ 
            (G (f (g (f x)))) ⁻¹ ∙ (ap f (H (g (f x))) ∙ G (f x)) ＝⟨ ap ((G (f (g (f x)))) ⁻¹ ∙_ ) square ⟩
            (G (f (g (f x)))) ⁻¹ ∙ (G (f (g (f x))) ∙ ap f (H x)) ＝⟨ aux (G (f (g (f x)))) (ap f (H x)) ⟩ 
            ap f (H x)                                            ∎ where

        aux : {X : 𝓤 ̇ } {x y z : X} (p : x ＝ y) (q : y ＝ z)
            → p ⁻¹ ∙ (p ∙ q) ＝ q
        aux (refl _) (refl _) = refl _

        HH : H (g (f x)) ＝ ap (g ∘ f) (H x)
        HH = nat-id-htpy (g ∘ f) H x

        nat-square : ap (f ∘ g ∘ f) (H x) ∙ (right-W G f) x ＝ (right-W G f) (g (f x)) ∙ ap f (H x)
        nat-square = nat-htpy (right-W G f) (H x)

        aux' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {x y : X} (p : x ＝ y) (f : X → Y) (g : Y → Z)
             → ap g (ap f p) ＝ ap (g ∘ f) p
        aux' (refl _) f g = refl _

        square : ap f (H (g (f x))) ∙ G (f x) ＝ G (f (g (f x))) ∙ ap f (H x)
        square = ap f (H (g (f x))) ∙ G (f x)           ＝⟨ refl _ ⟩  
            ap f (H (g (f x))) ∙ (right-W G f) x        ＝⟨ ap (λ z → ap f z ∙ (right-W G f) x) HH ⟩ 
            ap f (ap (g ∘ f) (H x)) ∙ (right-W G f) x   ＝⟨ ap (_∙ (right-W G f) x) (aux' (H x) (g ∘ f) f)  ⟩ 
            ap (f ∘ g ∘ f) (H x) ∙ (right-W G f) x      ＝⟨ nat-square ⟩ 
            (right-W G f) (g (f x)) ∙ ap f (H x)        ∎ 

is-equiv-is-contr : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) → is-equiv f → is-contr f
is-equiv-is-contr f isequiv = iscontr where
    hasinverse = is-equiv-has-inverse f isequiv
    iscohinv   = has-inverse-is-coh-invertible f hasinverse
    iscontr    = coherently-invertible-has-contractible-fibers f iscohinv


-- 
-- Teorema fundamental de los tipos identidad
-- 

tot : {A : 𝓤 ̇ } {B C : A → 𝓥 ̇ }
    → (f : Π x ꞉ A , (B x → C x))
    → (Σ x ꞉ A , B x → Σ x ꞉ A , C x)
tot f (x , y) = (x , f x y)

fib-tot-equiv : {A : 𝓤 ̇ } {B C : A → 𝓥 ̇ }
    → (f : Π x ꞉ A , (B x → C x)) → (t : Σ C)
    → fiber (tot f) t ≃ fiber (f (pr₁ t)) (pr₂ t)
fib-tot-equiv f t = ϕ t , p t where
    ϕ : (t : _) → fiber (tot f) t → fiber (f (pr₁ t)) (pr₂ t)
    ϕ (x , .(f x y₂)) ((.x , y₂) , refl .(x , f x y₂)) = y₂ , refl (f x y₂)

    ψ : (t : _) → fiber (f (pr₁ t)) (pr₂ t) → fiber (tot f) t
    ψ (x , .(f x x₁)) (x₁ , refl .(f x x₁)) = (x , x₁) , (refl (x , f x x₁))

    G : (t : _) → (ϕ t) ∘ (ψ t) ∼ id
    G (x , .(f x x₁)) (x₁ , refl .(f x x₁)) = refl (x₁ , refl (f x x₁))

    H : (t : _) → (ψ t) ∘ (ϕ t) ∼ id
    H (x , .(f x y₂)) ((.x , y₂) , refl .(x , f x y₂)) = refl _ 

    p : (t : _) → is-equiv (ϕ t)
    p t = (ψ t , G t) , (ψ t , H t)

family-of-equivalences : {A : 𝓤 ̇ } {B C : A → 𝓥 ̇ }
    → (f : Π x ꞉ A , (B x → C x))
    → 𝓤 ⊔ 𝓥 ̇ 
family-of-equivalences f = ∀ x → is-equiv (f x)

eq-implies-singleton : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → B ≃ A → is-singleton A → is-singleton B
eq-implies-singleton (f , (g₁ , h₁) , (g₂ , h₂)) singl-a = (g₂ (pr₁ singl-a)) , (λ b → ap g₂ (pr₂ singl-a (f b)) ∙ (h₂ b))

-- // TODO: terminar
-- tot-equiv-iff-familily-of-equiv : {A : 𝓤 ̇ } {B C : A → 𝓥 ̇ }
--     → (f : Π x ꞉ A , (B x → C x))
--     → (family-of-equivalences f) ⟷ is-equiv (tot f)
-- tot-equiv-iff-familily-of-equiv {_} {_} {A} {B} {C} f = {!    !} , {!   !}  where

--     eq-types : (x : A) → (c : C x) → fiber (tot f) (x , c) ≃ fiber (f x) c
--     eq-types x c = fib-tot-equiv f (x , c)

--     suffices-2 : (x : A) → (c : C x) 
--         → is-singleton (fiber (f x) c) ⟷ is-singleton (fiber (tot f) (x , c))
--     suffices-2 x c = (eq-implies-singleton (eq-types x c)) , (eq-implies-singleton (≃-sim (eq-types x c)))

--     suffices-1 : (∀ x → is-contr (f x)) ⟷ is-contr (tot f)
--     suffices-1 = {!   !} , {!   !}


-- FTIT-1 : {A : 𝓤 ̇ } → (a : A) → (B : A → 𝓥 ̇ ) → (f : Π x ꞉ A , ((a ＝ x) → B x))
--     → (family-of-equivalences f) ⟷ is-singleton (Σ B)
-- FTIT-1 = ?

-- FTIT-2 : {A : 𝓤 ̇ } → (a : A) → (B : A → 𝓥 ̇ ) → (f : Π x ꞉ A , ((a ＝ x) → B x))
--     → is-singleton (Σ B) ⟷ 

-- Proposiciones
is-prop : 𝓤 ̇  → 𝓤 ̇ 
is-prop X = (x y : X) → is-singleton (x ＝ y)

is-subsingleton : 𝓤 ̇  → 𝓤 ̇ 
is-subsingleton X = (x y : X) → x ＝ y

𝟘-is-subsingleton : is-subsingleton 𝟘 
𝟘-is-subsingleton x y = !𝟘 _ x

singleton-has-singleton-id : {X : 𝓤 ̇ } → is-singleton X 
    → (x y : X) → is-singleton (x ＝ y)
singleton-has-singleton-id (c , p) x y = ((p x ⁻¹) ∙ (p y)) , cases-z where
    cases-z : (z : x ＝ y) → p x ⁻¹ ∙ p y ＝ z
    cases-z (refl .x) = cases-p (p x) where
        cases-p : (z : c ＝ x) → z ⁻¹ ∙ z  ＝ refl x
        cases-p (refl .c) = refl (refl c)

singleton-is-subsingleton : {X : 𝓤 ̇ } → is-singleton X  → is-subsingleton X
singleton-is-subsingleton (c , p) x y = (p x ⁻¹) ∙ (p y)

𝟙-has-singleton-id : (x y : 𝟙) → is-singleton (x ＝ y)
𝟙-has-singleton-id * * = singleton-has-singleton-id 𝟙-is-singleton * * 

is-embedding : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (f : A → B) → 𝓤 ⊔ 𝓥 ̇ 
is-embedding f = (x y : _) → is-equiv (ap f {x} {y})

is-prop-is-subsingleton : {A : 𝓤 ̇ } → is-prop A → is-subsingleton A
is-prop-is-subsingleton p = λ x y → pr₁ (p x y) 

is-subsingleton-A-implies-singleton : {A : 𝓤 ̇ } → is-subsingleton A 
    → (A → is-singleton A)
is-subsingleton-A-implies-singleton sub a = a , (λ x → sub a x)

A-implies-singleton-const-*-embedding : {A : 𝓤 ̇ } → (A → is-singleton A)
    → is-embedding (!𝟙 {𝓤} {A})
A-implies-singleton-const-*-embedding a-impl-singl x y = (f , f-sec) , (f , f-ret) where
    f : !𝟙 x ＝ !𝟙 y → x ＝ y
    f _ = (pr₂ (a-impl-singl x ) x)⁻¹ ∙ (pr₂ (a-impl-singl x ) y)

    f-sec : (z : _) → ap !𝟙 (f z) ＝ z
    f-sec z = singleton-is-subsingleton (𝟙-has-singleton-id * *) (ap !𝟙 (f z)) z

    f-ret : (z : _) → f (ap !𝟙 z) ＝ z
    f-ret z = singleton-is-subsingleton (singleton-has-singleton-id (a-impl-singl x) x y) (f (ap !𝟙 z)) z

const-*-embedding-is-prop : {A : 𝓤 ̇ } → is-embedding (!𝟙 {𝓤} {A}) → is-prop A
const-*-embedding-is-prop emb = introduce-x-y where
    introduce-x-y : (x y : _) → is-singleton (x ＝ y)
    introduce-x-y x y = eq-implies-singleton (ap !𝟙 , emb x y) (𝟙-has-singleton-id * *) 

prop-iff-subsingleton : {X : 𝓤 ̇ } → is-prop X ⟷ is-subsingleton X
prop-iff-subsingleton = is-prop-is-subsingleton , (const-*-embedding-is-prop 
    ∘ A-implies-singleton-const-*-embedding 
    ∘ is-subsingleton-A-implies-singleton)

prop-equiv-iff-logically-equiv : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → {is-prop P} → {is-prop Q}
    → ((P ≃ Q) ⟷ (P ⟷ Q))
prop-equiv-iff-logically-equiv {_} {_} {P} {Q} {P-prop} {Q-prop} = (λ equiv → (pr₁ equiv) , pr₁ (pr₁ (pr₂ equiv))) ,
    λ p-iff-q → (pr₁ p-iff-q) , (((pr₂ p-iff-q) , λ x → is-prop-is-subsingleton Q-prop (pr₁ p-iff-q (pr₂ p-iff-q x)) x) , (pr₂ p-iff-q) , λ x → is-prop-is-subsingleton P-prop (pr₂ p-iff-q (pr₁ p-iff-q x)) x)

-- 
-- Univalencia
-- 

id-to-eq : {𝓤 : Universe} →  (A B : 𝓤 ̇ ) 
    → (A ＝ B) → (A ≃ B)
id-to-eq A A (refl _) = id , ((id , refl) , (id , refl))

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇ 
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → is-equiv (id-to-eq X Y)

funext𝓤 : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
funext𝓤 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ＝ g

left-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable f = {x x' : domain f} → f x ＝ f x' → x ＝ x'

equivs-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
    → is-equiv f → left-cancellable f 
equivs-are-lc f f-equiv fx-eq-fx' = f-lc fx-eq-fx' where
    f-inv : has-inverse f 
    f-inv = is-equiv-has-inverse f f-equiv

    g : codomain f → domain f 
    g = pr₁ f-inv

    gf-id : (x : _) → g (f x) ＝ x
    gf-id = pr₂ (pr₂ f-inv)

    f-lc : {x x' : _} → f x ＝ f x' → x ＝ x'
    f-lc {x} {x'} fx-eq-fx' = 
        x           ＝⟨ (gf-id x) ⁻¹    ⟩ 
        g (f x)     ＝⟨ ap g fx-eq-fx'  ⟩ 
        g (f x')    ＝⟨ gf-id x'        ⟩ 
        x'
        ∎ 
-- copy-paste BEGIN:
-- id-≃ : (X : 𝓤 ̇ ) → X ≃ X
-- id-≃ X = id , id-is-equiv

-- equiv-singleton-lemma : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X)
--     (f : (y : X) → x ＝ y → A y)
--     → ((y : X) → is-equiv (f y))
--     → is-singleton (Σ A)
-- equiv-singleton-lemma {𝓤} {𝓥} {X} {A} x f i = c , lemma where
--     c : Σ A 
--     c = x , f x (refl x)

--     lemma : (y : _) → c ＝ y
--     lemma (y , z) = {! i x  !}

-- univalence⇒ : is-univalent 𝓤
--             → (X : 𝓤 ̇ ) → is-singleton (Σ Y ꞉ 𝓤 ̇ , X ≃ Y)
-- univalence⇒ ua X = equiv-singleton-lemma X (id-to-eq X) (ua X)

-- univalence→ : is-univalent 𝓤
--     → (X : 𝓤 ̇ ) → is-subsingleton (Σ Y ꞉ 𝓤 ̇ , X ≃ Y)
-- univalence→ ua X = singleton-is-subsingleton (univalence⇒ ua X)

-- 𝔾-≃ : is-univalent 𝓤
--     → (X : 𝓤 ̇ ) (A : (Σ Y ꞉ 𝓤 ̇ , X ≃ Y) → 𝓥 ̇ )
--     → A (X , id-≃ X) → (Y : 𝓤 ̇ ) (e : X ≃ Y) → A (Y , e)

-- 𝔾-≃ {𝓤} ua X A a Y e = transport A p a where
--     t : Σ Y ꞉ 𝓤 ̇ , X ≃ Y
--     t = (X , id-≃ X)

--     p : t ＝ (Y , e)
--     p = univalence→ {𝓤} ua X t (Y , e)


-- ℍ-≃ : is-univalent 𝓤
--     → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
--     → A X (id-≃ X) → (Y : 𝓤 ̇ ) (e : X ≃ Y) → A Y e
-- ℍ-≃ ua X A = 𝔾-≃ ua X (Σ-induction A)

-- ℍ-equiv : is-univalent 𝓤
--     → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
--     → A X (𝑖𝑑 X) → (Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → A Y f
-- ℍ-equiv {𝓤} {𝓥} ua X A a Y f i = γ (f , i) where
--     B : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇
--     B Y (f , i) = A Y f

--     b : B X (id-≃ X)
--     b = a

--     γ : (e : X ≃ Y) → B Y e
--     γ = ℍ-≃ ua X B b Y

-- 𝕁-equiv : is-univalent 𝓤
--     → (A : (X Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
--     → ((X : 𝓤 ̇ ) → A X X (𝑖𝑑 X))
--     → (X Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → A X Y f
-- 𝕁-equiv ua A φ X = ℍ-equiv ua X (A X) (φ X)

-- // TODO: terminar
-- precomp-is-equiv : {𝓤 : Universe} → is-univalent 𝓤
--     → (X Y : 𝓤 ̇ ) (f : X → Y)
--     → is-equiv f
--     → (Z : 𝓤 ̇ ) → is-equiv (λ (g : Y → Z) → g ∘ f)
-- precomp-is-equiv {𝓤} ua = {!   !} 
-- 
-- univ-implies-funext : {𝓤 𝓥 : Universe} → is-univalent 𝓥 → funext𝓤 𝓤 𝓥 
-- univ-implies-funext {𝓤} {𝓥} ua {X} {Y} {f₀} {f₁} = γ where

--     Δ : 𝓥 ̇
--     Δ = Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , y₀ ＝ y₁

--     δ : Y → Δ
--     δ y = (y , y , refl y)

--     π₀ π₁ : Δ → Y
--     π₀ (y₀ , y₁ , p) = y₀
--     π₁ (y₀ , y₁ , p) = y₁

--     δ-is-equiv : is-equiv δ
--     δ-is-equiv = invertible-is-equivalence δ (π₀ , η , ε) where
--         η : (y : Y) → π₀ (δ y) ＝ y
--         η y = refl y

--         ε : (d : Δ) → δ (π₀ d) ＝ d
--         ε (y , y , refl y) = refl (y , y , refl y)

--     φ : (Δ → Y) → (Y → Y)
--     φ π = π ∘ δ

--     φ-is-equiv : is-equiv φ
--     φ-is-equiv = precomp-is-equiv ua Y Δ δ δ-is-equiv Y

--     p : φ π₀ ＝ φ π₁
--     p = refl (𝑖𝑑 Y)

--     q : π₀ ＝ π₁
--     q = equivs-are-lc φ φ-is-equiv p 

--     γ : f₀ ∼ f₁ → f₀ ＝ f₁
--     γ h = ap (λ π x → π (f₀ x , f₁ x , h x)) q

-- copy-paste END

postulate univalence-axiom : (𝓤 : Universe) → is-univalent 𝓤
postulate funext : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ＝ g
-- funext : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ＝ g
-- funext {_} {𝓥} = univ-implies-funext (univalence-axiom 𝓥)

Eq-copr : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A + B) → (A + B) → 𝓤 ⊔ 𝓥 ̇ 
Eq-copr {𝓤} {𝓥} (inl x) (inl x') = raise (𝓤 ⊔ 𝓥) (x ＝ x')
Eq-copr {𝓤} {𝓥} (inl x) (inr y') = raise (𝓤 ⊔ 𝓥) 𝟘
Eq-copr {𝓤} {𝓥} (inr y) (inl x') = raise (𝓤 ⊔ 𝓥) 𝟘
Eq-copr {𝓤} {𝓥} (inr y) (inr y') = raise (𝓤 ⊔ 𝓥) (y ＝ y')  

Eq-copr-refl : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (p : A + B) → Eq-copr p p 
Eq-copr-refl (inl x) = map-raise (refl x)
Eq-copr-refl (inr y) = map-raise (refl y)

Eq-copr-eq : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (s : A + B) → (t : A + B) → (s ＝ t)
    → Eq-copr s t
Eq-copr-eq s s (refl s) = Eq-copr-refl s

Eq-Eq-copr : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (s : A + B) → (t : A + B) → Eq-copr s t 
    → (s ＝ t)
Eq-Eq-copr (inl x) (inl x') s-eq-copr-t = ap inl (down s-eq-copr-t)
Eq-Eq-copr (inl x) (inr y') s-eq-copr-t = !𝟘 _ (down s-eq-copr-t)
Eq-Eq-copr (inr y) (inl x') s-eq-copr-t = !𝟘 _ (down s-eq-copr-t)
Eq-Eq-copr (inr y) (inr y') s-eq-copr-t = ap inr (down s-eq-copr-t)

Eq-copr-eq-has-inverse : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (s : A + B) → (t : A + B)
    → has-inverse (Eq-copr-eq s t) 
Eq-copr-eq-has-inverse s t = Eq-Eq-copr s t , (right-inverse s t , left-inverse s t) where

    left-inverse : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (s : A + B) → (t : A + B)
        → (x : _) → Eq-Eq-copr s t (Eq-copr-eq s t x) ＝ x
    left-inverse (inl x) (inl x) (refl (inl x)) = refl (refl (inl x))
    left-inverse (inr y) (inr y) (refl (inr y)) = refl (refl (inr y))

    right-inverse : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (s : A + B) → (t : A + B)
        → (x : _) → Eq-copr-eq s t (Eq-Eq-copr s t x) ＝ x
    right-inverse (inl x) (inl x) (map-raise (refl x)) = refl (map-raise (refl x))
    right-inverse (inl x) (inr y') z = !𝟘 _ (down z)
    right-inverse (inr y) (inl x') z = !𝟘 _ (down z)
    right-inverse (inr y) (inr y) (map-raise (refl y)) = refl (map-raise (refl y))

-- Aplicación de univalencia: 
prop-logically-equiv-implies-eq : {P Q : 𝓤 ̇ }→ {is-prop P} → {is-prop Q}
    → (P ⟷ Q) → (P ＝ Q) 
prop-logically-equiv-implies-eq {𝓤} {P} {Q} {P-prop} {Q-prop} p-iff-q = pr₁ (pr₁ (univalence-axiom 𝓤 P Q)) (rl-implication (prop-equiv-iff-logically-equiv {𝓤} {𝓤} {P} {Q} {P-prop} {Q-prop}) p-iff-q)

    
    