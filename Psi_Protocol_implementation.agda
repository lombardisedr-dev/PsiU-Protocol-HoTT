{-# OPTIONS --cubical --safe #-}

module Psi_Protocol_implementation where

-- ========================================================================
-- 1. FONDAMENTA OMOTOPICHE PRIMITIVE NATIVER
-- ========================================================================

-- Carichiamo l'intervallo nativo e le sue operazioni incluse nel compilatore
open import Agda.Primitive.Cubical renaming (primHComp to hcomp; primTransp to transp)
open import Agda.Builtin.Cubical.Path public

-- Definizione nativa dei livelli per evitare di importare pacchetti esterni
open import Agda.Primitive public using (Level; lzero) renaming (lsuc to lsuc-prim)

lsuc : Level → Level
lsuc = lsuc-prim

Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ

data ℕ : Type lzero where
  zero : ℕ
  suc  : ℕ → ℕ

-- Usiamo la primitiva nativa di negazione dell'intervallo cubico primINeg
sym : {ℓ : Level} {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym p = λ i → p (primINeg i)

-- ========================================================================
-- 2. GEOMETRIA SST (Semi-Simplicial Types) DIPENDENTE
-- ========================================================================

record ComplessoSST : Type (lsuc lzero) where
  constructor CostruisciSST
  field
    Punti     : Type lzero
    Segmenti  : Punti → Punti → Type lzero
    Triangoli : (v0 v1 v2 : Punti) 
              → (s01 : Segmenti v0 v1) 
              → (s12 : Segmenti v1 v2) 
              → (s02 : Segmenti v0 v2) 
              → Type lzero

-- ========================================================================
-- 3. PROPRIETÀ GEOMETRICA (Test d'Involuzione Cubica)
-- ========================================================================

inv-involutiva : {A : Type lzero} {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
inv-involutiva p i j = p (primINeg (primINeg j))

-- ========================================================================
-- 4. GERARCHIA INDUTTIVA DEL PROTOCOLLO PSIU
-- ========================================================================

record LivelloCoerenza (n : ℕ) : Type (lsuc lzero) where
  constructor CoherenceLevel
  field
    struttura : ComplessoSST
    identita  : (p : ComplessoSST.Punti struttura) → p ≡ p

PSIU-Inductive-Hierarchy : (n : ℕ) → LivelloCoerenza n
PSIU-Inductive-Hierarchy n = record
  { struttura = record
      { Punti     = ℕ
      ; Segmenti  = λ x y → x ≡ y
      ; Triangoli = λ v0 v1 v2 s01 s12 s02 → v0 ≡ v2
      }
  ; identita  = λ x i → x
  }
