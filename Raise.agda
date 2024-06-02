{-# OPTIONS --without-K --exact-split --auto-inline #-}
open import Universes public

data raise (𝓥 : Universe) {𝓤 : Universe} (A : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
    map-raise : A → raise 𝓥 A

down : {𝓤 𝓥 : Universe} {A : 𝓤 ̇ }
    → raise 𝓥 A → A
down (map-raise x) = x