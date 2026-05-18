{-# OPTIONS --cubical --safe #-}

module Smascheramento where

open import Psi_Protocol_implementation
open import Agda.Builtin.Nat
open import Agda.Builtin.Cubical.Path

-- TEST DI ONESTÀ LOGICA:
-- Se la gerarchia PSIU è corretta, non dovrebbe essere possibile
-- definire un triangolo tra vertici che non sono uguali, 
-- perché l'identità (≡) tra 0 e 1 è impossibile da dimostrare.

smascheramento-onesto : (s01 : 0 ≡ 1) (s12 : 1 ≡ 2) (s02 : 0 ≡ 2)
  → ComplessoSST.Triangoli (LivelloCoerenza.struttura (PSIU-Inductive-Hierarchy 1)) 0 1 2 s01 s12 s02
  → 0 ≡ 2
smascheramento-onesto s01 s12 s02 Tri = Tri

-- Se carichi questo file in Agda o lo fai girare in una Action:
-- 1. Se il compilatore dà ERRORE su 's01 : 0 ≡ 1', il sistema è onesto (non puoi creare cammini falsi).
-- 2. SE COMPILA (esce VERDE), allora l'autore ha ridefinito l'identità (≡) 
--    o il concetto di Triangolo in modo che NON dipenda dalla verità matematica dei vertici.
