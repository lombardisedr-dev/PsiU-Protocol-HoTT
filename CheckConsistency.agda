{-# OPTIONS --cubical --safe #-}
module CheckConsistency where

-- Importa l'intera libreria Cubical ufficiale
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

-- Importa il tuo protocollo
open import PsiU 

-- Prova di compatibilità: verifichiamo che il tuo 'sym' sia coerente con quello ufficiale
compatibility-test : {A : Set} {x y : A} (p : x ≡ y) → sym p ≡ Cubical.Foundations.Prelude.sym p
compatibility-test p = refl
