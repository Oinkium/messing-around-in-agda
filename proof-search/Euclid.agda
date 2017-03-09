module Euclid where

open import Data.Nat

open import Data.Product

open import Data.Nat.DivMod

open import Data.Fin

data ℕ₁ : Set where
  one : ℕ₁
  succ : ℕ₁ → ℕ₁

i : ℕ₁ → ℕ
i one = suc zero
i (succ N) = suc (i N)

-- Division with remainder.
division : (a : ℕ) → ℕ₁ → (ℕ × (Fin a))
division a b = ( (a div (i b)) , (a mod (i b)) )


