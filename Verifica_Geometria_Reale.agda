{-# OPTIONS --cubical --safe #-}
module Verifica_Geometria_Reale where

open import Psi_Protocol_implementation
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

-- Tentiamo di dimostrare che se esiste un Triangolo, 
-- allora esiste un cammino coerente tra i vertici.
-- Questo verifica se il triangolo "connette" effettivamente i punti.
test-connessione : (v0 v1 v2 : ℕ) 
                 → (s01 : v0 ≡ v1) (s12 : v1 ≡ v2) (s02 : v0 ≡ v2)
                 → (Tri : ComplessoSST.Triangoli (LivelloCoerenza.struttura (PSIU-Inductive-Hierarchy 1)) v0 v1 v2 s01 s12 s02)
                 → v0 ≡ v2
test-connessione v0 v1 v2 s01 s12 s02 Tri = Tri -- Se compila, la connessione base esiste
