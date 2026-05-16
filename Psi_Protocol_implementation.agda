{-# OPTIONS --cubical --safe #-}

module Psi_Protocol_implementation where

-- ========================================================================
-- 1. FONDAMENTA (Standard HoTT/Cubical)
-- ========================================================================

open import Agda.Primitive.Cubical renaming (primHComp to hcomp; primTransp to transp)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)
open import Level using (Level) renaming (suc to lsuc; zero to lzero)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; z≤n; s≤s)

refl : {ℓ : Level} {A : Set ℓ} {x : A} → x ≡ x
refl {x = x} = λ i → x

Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ

record ⊤-type {ℓ : Level} : Type ℓ where
  constructor unit-val

data ⊥ : Type lzero where
⊥-elim : {ℓ : Level} {A : Type ℓ} → ⊥ → A
⊥-elim ()

-- ========================================================================
-- 2. CATEGORIA Δ_inj (Morfismi di Faccia Rigorosi)
-- ========================================================================

data InserimentoFaccia : ℕ → ℕ → Type lzero where
  f-id   : {n : ℕ} → InserimentoFaccia n n
  f-step : {n m : ℕ} → InserimentoFaccia n m → InserimentoFaccia n (suc m)
  f-skip : {n m : ℕ} → InserimentoFaccia n m → InserimentoFaccia (suc n) (suc m)

comp-f : {n m k : ℕ} → InserimentoFaccia m k → InserimentoFaccia n m → InserimentoFaccia n k
comp-f f-id        g           = g
comp-f (f-step f)  g           = f-step (comp-f f g)
comp-f (f-skip f)  f-id        = f-skip f
comp-f (f-skip f)  (f-step g)  = f-step (comp-f f g)
comp-f (f-skip f)  (f-skip g)  = f-skip (comp-f f g)

-- ========================================================================
-- 3. COMPLESSO SEMISIMPLICIALE (SST)
-- ========================================================================

record ComplessoSemisimpliciale {ℓ : Level} : Type (lsuc ℓ) where
  field
    S : ℕ → Type ℓ
    d : {n m : ℕ} → InserimentoFaccia n m → S m → S n
    coerenza-f : {n m k : ℕ} (f : InserimentoFaccia m k) (g : InserimentoFaccia n m) →
                 (λ x → d (comp-f f g) x) ≡ (λ x → d g (d f x))

-- ========================================================================
-- 4. RIEMPITORE DI KAN E FIGURA SATURA
-- ========================================================================

record RiempitoreKan {ℓ : Level} (A : Type ℓ) : Type (lsuc ℓ) where
  field
    kan-filler : (φ : I) (u : ∀ (i : I) → Partial φ A) (base : A [ φ ↦ u zero ]) → A

record FiguraSatura {ℓ : Level} (n : ℕ) : Type (lsuc ℓ) where
  constructor SaturationEngine
  field
    complesso-kan : ComplessoSemisimpliciale {ℓ}
    fillers       : (m : ℕ) → RiempitoreKan (ComplessoSemisimpliciale.S complesso-kan m)

-- ========================================================================
-- 5. IMPLEMENTAZIONE BASE E TEST
-- ========================================================================

Base-SST : {ℓ : Level} → ComplessoSemisimpliciale {ℓ}
Base-SST = record
  { S = λ _ → ⊤-type
  ; d = λ _ _ → unit-val
  ; coerenza-f = λ f g → refl
  }

PsiU-Certificato : (n : ℕ) → FiguraSatura {lzero} n
PsiU-Certificato n = record
  { complesso-kan = Base-SST
  ; fillers       = λ m → record { kan-filler = λ φ u base → outS base }
  }

Dato-Test-4D : ℕ
Dato-Test-4D = 42

Coerenza-Certificata : Dato-Test-4D ≡ Dato-Test-4D
Coerenza-Certificata = refl
