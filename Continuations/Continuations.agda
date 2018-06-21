open import Data.Empty
open import Function
open import Relation.Nullary.Negation
open import Level
open import Category.Monad.Indexed

module Continuations where

open RawIMonad (¬¬-Monad {Level.zero})

module ContinuationImplication where
  open import Relation.Nullary

  infixr 1 _⇒_

  _⇒_ : Set → Set → Set
  A ⇒ B = A → ¬ ¬ B

open ContinuationImplication

call-with-current-continuation : ∀ {P Q : Set} → ((P ⇒ Q) ⇒ P) ⇒ P
call-with-current-continuation = call/cc

infix 3 ¬_

¬_ : Set → Set
¬_ A = A ⇒ ⊥

¬¬ : Set → Set
¬¬ P = ¬ ¬ P

law-of-excluded-middle : ∀ {P : Set} → ¬ ¬ P ⇒ P
law-of-excluded-middle = λ f → call/cc (λ ¬p →  ⊥-elim =<< (f ¬p))

law-of-excluded-middle2 : ∀ {P : Set} → ¬ ¬ P ⇒ P
law-of-excluded-middle2 = λ z z₁ → z (λ z₂ z₃ → z₃ (z₁ z₂)) (λ z₂ → z₂)


