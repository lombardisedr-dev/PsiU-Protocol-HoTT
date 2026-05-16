{-# OPTIONS --cubical --safe #-}

module Test_Associativity where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import PsiU
open import Model_Blockchain

-- Test: L'unione dei blocchi (transazioni) è associativa?
-- Se p, q, r sono tre validazioni consecutive, (p ∙ q) ∙ r deve essere uguale a p ∙ (q ∙ r)
blockchain-assoc : {tx1 tx2 tx3 tx4 : ℕ} 
                   (p : tx1 ≡ tx2) (q : tx2 ≡ tx3) (r : tx3 ≡ tx4)
                 → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
blockchain-assoc p q r = assoc p q r
