{-# OPTIONS --without-K --exact-split --auto-inline #-}
module PropTruncations where

open import MLTT
open import Decidability

record subsingleton-truncations-exist : 𝓤ω where
    field
        ∥_∥                  : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
        ∥∥-is-subsingleton   : {𝓤 : Universe} {X : 𝓤 ̇ } → is-subsingleton ∥ X ∥
        ∣_∣                  : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
        ∥∥-recursion         : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ }
                            → is-subsingleton P → (X → P) → ∥ X ∥ → P
    infix 0 ∥_∥

module Properties(pt : subsingleton-truncations-exist) where
    open subsingleton-truncations-exist pt public

    -- Propiedades sobre truncados proposicionales y proposiciones

    neg-of-prop-is-prop : {A : 𝓤 ̇ } → is-subsingleton A → is-subsingleton (¬ A)
    neg-of-prop-is-prop pA x y = funext λ z → 𝟘-is-subsingleton (x z) (y z)

    implication-is-prop : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → is-subsingleton A → is-subsingleton B
        → is-subsingleton (A → B)
    implication-is-prop pA pB f₁ f₂ = funext (λ x → pB (f₁ x) (f₂ x))


    dec-iff-trunc-dec : {A : 𝓤 ̇ } → (∥ decidable A ∥ ⟷ decidable ∥ A ∥ )
    dec-iff-trunc-dec {𝓤} {A} = lr-lemma , rl-lemma where
        lr-lemma : ∥ decidable A ∥ → decidable ∥ A ∥
        lr-lemma pa = ∥∥-recursion is-subsingleton-dec-∥A∥ dec-A-imp-dec-∥A∥ pa where
            is-subsingleton-dec-∥A∥ : is-subsingleton (decidable ∥ A ∥) 
            is-subsingleton-dec-∥A∥ (yes x) (yes y) = ap yes (∥∥-is-subsingleton x y)
            is-subsingleton-dec-∥A∥ (yes x) (no y) = !𝟘 _ (y x)
            is-subsingleton-dec-∥A∥ (no x) (yes y) = !𝟘 _ (x y)
            is-subsingleton-dec-∥A∥ (no x) (no y) = ap no (neg-of-prop-is-prop ∥∥-is-subsingleton x y)

            dec-A-imp-dec-∥A∥ : decidable A → decidable ∥ A ∥ 
            dec-A-imp-dec-∥A∥ (yes x) = yes ∣ x ∣
            dec-A-imp-dec-∥A∥ (no x) = no (∥∥-recursion 𝟘-is-subsingleton x)

        rl-lemma : decidable ∥ A ∥ → ∥ decidable A ∥
        rl-lemma (yes x) = ∥∥-recursion ∥∥-is-subsingleton (λ z → ∣ yes z ∣) x
        rl-lemma (no x) = ∣ no (λ y → x ∣ y ∣) ∣

    dec-implies-get-element : {A : 𝓤 ̇ } → decidable A → ∥ A ∥ → A 
    dec-implies-get-element {_} {A} (yes x) pA = x
    dec-implies-get-element {_} {A} (no x) pA = !𝟘 _ (∥∥-recursion 𝟘-is-subsingleton x pA)




    