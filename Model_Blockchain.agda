{-# OPTIONS --cubical --safe #-}
module Model_Blockchain where

open import PsiU
open import Agda.Builtin.Sigma

-- Definiamo un modello dove i Punti sono transazioni (ℕ per semplicità)
-- e i Segmenti sono prove di validazione tra transazioni.
BlockchainModel : LivelloCoerenza zero
BlockchainModel = record
  { struttura = record
    { Punti     = ℕ
    ; Segmenti  = λ tx1 tx2 → tx1 ≡ tx2 -- Una transazione è valida se è coerente
    ; Triangoli = λ v0 v1 v2 s01 s12 s02 → Σ ℕ (λ hash → v0 ≡ v2) -- Coerenza del blocco
    }
  ; identita = λ x i → x
  }
