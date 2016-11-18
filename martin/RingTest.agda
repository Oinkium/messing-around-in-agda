module RingTest where

open import Data.Nat.Properties as NatProp
open NatProp.SemiringSolver
open import Data.Nat
open import Relation.Binary.PropositionalEquality

eqn : ∀ a b c → suc (_+_ (_+_ a b) c) ≡ _+_ a (suc (_+_ b c))
eqn = solve 3 (λ a b c → con 1 :+ ((a :+ b) :+ c) := a :+ (con 1 :+ (b :+ c))) refl

-- 
