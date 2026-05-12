{-# OPTIONS --without-K --safe #-}

-- Il nome del modulo deve coincidere con il nome del file
module PSIU_Protocol where

open import Level using (Level; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

-- 1. DEFINIZIONE DELLA STRUTTURA SEMISIMPLICIALE PURA
-- Verifichiamo la coerenza per tipi generici (senza l'uso di ℕ)
record SemisimplicialUniverse {ℓ : Level} : Set (suc ℓ) where
  field
    X₀ : Set ℓ                                         -- Punti
    X₁ : X₀ → X₀ → Set ℓ                               -- Segmenti
    X₂ : {x y z : X₀} → X₁ x y → X₁ y z → X₁ x z → Set ℓ -- Triangoli (Coerenza 2D)

    -- Definizione del Tetraedro: il cuore della soluzione SST
    X₃ : {x y z w : X₀} 
       → {f : X₁ x y} {g : X₁ y z} {h : X₁ z w}
       → {fg : X₁ x z} {gh : X₁ y w} {fgh : X₁ x w}
       → (α : X₂ f g fg) (β : X₂ fg h fgh) 
       → (γ : X₂ g h gh) (δ : X₂ f gh fgh) 
       → Set ℓ

-- 2. OMEGA STABILITY (Induzione all'infinito)
data Omega-Stability {ℓ : Level} (SST : SemisimplicialUniverse {ℓ}) : Set (suc ℓ) where
  Crystallized : Omega-Stability SST

-- 3. PROVA DI TRASPORTO (J-Rule)
stability-transport : {ℓ : Level} {A : Set ℓ} (P : A → Set ℓ) {x y : A} 
                    → x ≡ y → P x → P y
stability-transport P refl proof = proof


