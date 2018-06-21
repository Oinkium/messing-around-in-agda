module Classical where

open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Function

call/cc1 : {P Q : Set} → ((P → Q) → ¬ ¬ P) → ¬ ¬ P
call/cc1 hyp ¬p = hyp (λ p → ⊥-elim (¬p p)) ¬p

call/cc-var : {P Q : Set} →  Stable P → ((P → Q) → P) → P
call/cc-var stable hyp = stable (λ ¬p → ¬p (hyp (λ p → ⊥-elim (¬p p))))

