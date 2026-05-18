{-# OPTIONS --cubical --safe #-}
module Psi_Protocol_implementation where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

-- IL NECESSARIO: La composizione reale dei cammini
_∙_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q i = hcomp (λ j → λ where (i = i0) → x ; (i = i1) → q j) (p i)

-- LA STRUTTURA SST RIGOROSA
record ComplessoSST : Set1 where
  field
    Punti : Set
    Segmenti : Punti → Punti → Set
    -- Qui il filtro risuona: il triangolo DEVE chiudere lo scostamento
    Triangoli : (v0 v1 v2 : Punti) (s01 : Segmenti v0 v1) (s12 : Segmenti v1 v2) (s02 : Segmenti v0 v2) → Set

-- GERARCHIA DINAMICA (Sostituisce quella statica fallace)
record LivelloCoerenza (n : ℕ) : Set1 where
  field
    struttura : ComplessoSST

PSIU-Inductive-Hierarchy : (n : ℕ) → LivelloCoerenza n
PSIU-Inductive-Hierarchy n = record { struttura = record
  { Punti = ℕ
  ; Segmenti = λ x y → x ≡ y
  ; Triangoli = λ v0 v1 v2 s01 s12 s02 → (s01 ∙ s12) ≡ s02 } }
