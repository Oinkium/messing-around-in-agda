module NatPrint where

open import Data.Nat
  renaming (ℕ to Nat ; zero to biZero ; suc to biSuc)
open import Data.Nat.Show
open import Data.Unit
open import Agda.Builtin.String
open import Function
open import Coinduction


data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

toNat : ℕ → Nat
toNat zero = biZero
toNat (suc n) = biSuc (toNat n)

open import IO

printOutNaturalNumbers : (ℕ → String) → IO ⊤
printOutNaturalNumbers f = ♯ putStrLn(f zero) >>= (λ _ → ♯ (printOutNaturalNumbers (f ∘ suc)))

main = run(printOutNaturalNumbers(show ∘ toNat))
