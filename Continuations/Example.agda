module Example where

module UsingStdLib where
  open import Relation.Nullary

  ¬¬ : Set → Set
  ¬¬ P = ¬ ¬ P

module ByHand where
  open import Data.Empty
  open import Level

  -- Code copied from Relation.Nullary
  infix 3 ¬_

  ¬_ : Set → Set
  ¬ P = P → ⊥

  ¬¬ : Set → Set
  ¬¬ P = ¬ ¬ P
