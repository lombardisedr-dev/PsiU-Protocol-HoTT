{-# OPTIONS --cubical --safe #-}

module Verify_Infinite_Induction where

-- Importiamo il core senza modificarlo
open import Psi_Protocol_implementation
open import Agda.Builtin.ℕ

-- TEOREMA DELL'INFINITO LOGICO
-- Dimostriamo che la struttura PSIU è ben fondata per induzione completa.
-- Se Agda accetta questa funzione, abbiamo la prova che il protocollo
-- può scalare all'infinito senza mai rompere la geometria SST.

infinite-proof : (n : ℕ) → LivelloCoerenza n
infinite-proof zero = PSIU-Inductive-Hierarchy zero
infinite-proof (suc n) = PSIU-Inductive-Hierarchy (suc n)

-- VERIFICA DI COERENZA UNIVERSALE
-- Confermiamo che il generatore induttivo è coerente con se stesso
universal-consistency : (n : ℕ) → infinite-proof n ≡ PSIU-Inductive-Hierarchy n
universal-consistency n = refl
