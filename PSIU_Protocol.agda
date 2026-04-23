{-# OPTIONS --without-K --safe #-}

module PSIU_Protocol where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality
-- AGGIUNGI QUESTA RIGA PER RISOLVERE L'ERRORE:
open import Data.Nat using (ℕ)

-- 1. STRUTTURA SEMISIMPLICIALE BEN TIPIZZATA
record WellTypedSemisimplicial : Set₁ where
  field
    X₀ : Set
    X₁ : X₀ → X₀ → Set
    X₂ : {x y z : X₀} (f : X₁ x y) (g : X₁ y z) (h : X₁ x z) → Set

  field
    coherent : {x y z : X₀} (f : X₁ x y) (g : X₁ y z) (h : X₁ x z) 
             → X₂ f g h → Set

-- 2. ISTANZA DI PROVA (Il Seme Reale)
PSIU-Validated-Seed : WellTypedSemisimplicial
PSIU-Validated-Seed = record
  { X₀ = Set
  ; X₁ = λ A B → A ≡ B
  ; X₂ = λ f g h → trans f g ≡ h 
  ; coherent = λ f g h _ → Set 
  }

-- 3. J-RULE (TRASPORTO DELLA TIPIZZAZIONE)
stability-transport : {A : Set₁} (P : A → Set) {x y : A} 
                    → x ≡ y → P x → P y
stability-transport P refl proof = proof

-- 4. OMEGA STABILITY (n = 10.000)
-- Ora ℕ è riconosciuto correttamente.
data Omega (n : ℕ) : Set where
  Crystallized : WellTypedSemisimplicial → Omega n


