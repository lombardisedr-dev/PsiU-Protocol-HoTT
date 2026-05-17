{-# OPTIONS --cubical --safe #-}
module Verifica_Analisi_Profonda where

open import Psi_Protocol_implementation
open import Agda.Builtin.Cubical.Path

-- TEST DI ANALISI: Proprietà di riempimento (Filler)
-- Vogliamo vedere se, dato un "angolo" (due segmenti s01 e s12), 
-- la struttura ci obbliga a una composizione specifica (s01 ∙ s12).
analisi-filler : (v0 v1 v2 : ℕ) (s01 : v0 ≡ v1) (s12 : v1 ≡ v2)
               → (SST : ComplessoSST)
               → SST ≡ LivelloCoerenza.struttura (PSIU-Inductive-Hierarchy 1)
               → Σ (v0 ≡ v2) (λ s02 → ComplessoSST.Triangoli SST v0 v1 v2 s01 s12 s02)
analisi-filler v0 v1 v2 s01 s12 SST eq = 
  (s01 ∙ s12) , (transport (λ i → ComplessoSST.Triangoli (eq i) v0 v1 v2 s01 s12 (s01 ∙ s12)) (s01 ∙ s12))
