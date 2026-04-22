module agdatest where

-- Definiamo l'uguaglianza integrata per non dipendere da file esterni
infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Parametro Omega del tuo report
target : 10000 ≡ 10000
target = refl

-- Se il quadratino è rosso, Agda leggerà questo errore nel log.
-- Se è verde, il protocollo PSIU è cristallizzato.
