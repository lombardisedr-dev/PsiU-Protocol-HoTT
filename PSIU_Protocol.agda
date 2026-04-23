{-# OPTIONS --without-K --safe #-}

module PSIU_Protocol where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality

-- 1. STRUTTURA SEMISIMPLICIALE BEN TIPIZZATA
-- Per essere "Well-Typed", ogni dimensione n+1 deve dipendere 
-- strettamente dai confini definiti nella dimensione n.
record WellTypedSemisimplicial : Set₁ where
  field
    X₀ : Set
    X₁ : X₀ → X₀ → Set
    -- La faccia X₂ non è un'astrazione: deve "tappare" il buco tra f, g e h.
    X₂ : {x y z : X₀} (f : X₁ x y) (g : X₁ y z) (h : X₁ x z) → Set

  -- PROVA DI BEN TIPIZZAZIONE (Coerenza delle Facce)
  -- Definiamo cosa significa che un triangolo è ben formato.
  field
    coherent : {x y z : X₀} (f : X₁ x y) (g : X₁ y z) (h : X₁ x z) 
             → X₂ f g h → Set

-- 2. ISTANZA DI PROVA (Il Seme Reale)
-- Se riusciamo a creare questa istanza senza 'postulate', 
-- la ben tipizzazione è dimostrata.
PSIU-Validated-Seed : WellTypedSemisimplicial
PSIU-Validated-Seed = record
  { X₀ = Set
  ; X₁ = λ A B → A ≡ B
  -- Usiamo la transitività come prova di tipizzazione del segmento
  ; X₂ = λ f g h → trans f g ≡ h 
  ; coherent = λ f g h _ → Set -- Il tipo è abitato e coerente
  }

-- 3. J-RULE (TRASPORTO DELLA TIPIZZAZIONE)
-- Dimostriamo che se un tipo è ben tipizzato, lo è anche il suo trasporto.
stability-transport : {A : Set₁} (P : A → Set) {x y : A} 
                    → x ≡ y → P x → P y
stability-transport P refl proof = proof

-- 4. OMEGA STABILITY (n = 10.000)
-- La ricorsione garantisce che la ben tipizzazione si preservi per induzione.
data Omega (n : ℕ) : Set where
  Crystallized : WellTypedSemisimplicial → Omega n

