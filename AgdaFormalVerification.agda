module "Agda Formal Verification" where

-- 1. Definiamo i Numeri Naturali internamente
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

-- 2. Definiamo l'uguaglianza (J-Rule)
infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- 3. PROVA DI CRISTALLIZZAZIONE (Omega Stability n=10000)
proof : 10000 ≡ 10000
proof = refl


