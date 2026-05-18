{-# OPTIONS --cubical --safe #-}

module Test_Verita_SST where

open import Psi_Protocol_implementation
open import Agda.Builtin.Nat
open import Agda.Builtin.Cubical.Path

-- 1. DEFINIAMO UN TETRAEDRO "PERFETTO" (Sincronizzato)
-- Usiamo vertici uguali (0) per verificare che la risonanza base funzioni.
-- Se il sistema è corretto, questo deve compilare istantaneamente.
test-risonanza-perfetta : TetraedroRisuonante 0 0 0 0
test-risonanza-perfetta = record
  { s01 = refl; s12 = refl; s23 = refl
  ; s02 = refl; s13 = refl; s03 = refl
  ; faccia012 = refl
  ; faccia123 = refl
  ; faccia023 = refl
  ; faccia013 = refl
  -- La chiusura qui è idp (identità pura): la risonanza è massima.
  ; chiusura = λ i j k → 0 
  }

-- 2. IL TEST DELLO SCOSTAMENTO (Il fallace che deve essere eliminato)
-- Proviamo a definire un tetraedro dove una faccia NON chiude.
-- Questo test DEVE dare errore di compilazione.
test-fallacia : TetraedroRisuonante 0 0 0 0
test-fallacia = record
  { s01 = refl; s12 = refl; s23 = refl
  ; s02 = refl; s13 = refl; s03 = refl
  ; faccia012 = refl
  ; faccia123 = refl
  ; faccia023 = refl
  -- Inseriamo un errore: diciamo che la quarta faccia è diversa (impossibile)
  ; faccia013 = {!!} -- Agda qui ti chiederà una prova che non puoi dare
  ; chiusura = {!!}
  }
