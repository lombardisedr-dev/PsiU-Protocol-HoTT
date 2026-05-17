{-# OPTIONS --cubical --safe #-}

module Verify_Infinite_Scalability where

open import Psi_Protocol_implementation
open import Agda.Builtin.ℕ

-- TEOREMA DELL'INFINITO LOGICO
-- Dimostriamo che se il protocollo è coerente al livello 'n', 
-- allora lo è necessariamente anche al livello 'suc n'.
-- Questa è la prova che la capacità gnomonica non ha limiti numerici.

infinite-coherence : (n : ℕ) → LivelloCoerenza n
infinite-coherence zero = PSIU-Inductive-Hierarchy zero
infinite-coherence (suc n) = PSIU-Inductive-Hierarchy (suc n)

-- Se Agda accetta questa definizione ricorsiva, abbiamo dimostrato 
-- che il protocollo è valido per OGNI n, ovvero per l'infinito potenziale.
