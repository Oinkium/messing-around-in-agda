module PrimeSequence where

open import Coinduction
open import Function
open import Data.String
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Data.Nat
open import Data.Nat.Primality
open import Data.Nat.Show

data coℕ : Set where
  zero : coℕ
  suc : ∞ coℕ → coℕ

fromℕ : ℕ → coℕ
fromℕ ℕ.zero = zero
fromℕ (ℕ.suc n) = suc (♯ (fromℕ n))

getNextPrime : ℕ → coℕ
getNextPrime n with prime? n
... | yes pr = fromℕ n
... | no com = getNextPrime (suc n)

primes : ℕ → ℕ
primes zero = getNextPrime zero
primes (suc n) = getNextPrime (suc (primes n))

open import IO

printResults : (ℕ → String) → IO ⊤
printResults f = ♯ (putStrLn(f zero)) >>= (λ _ → ♯ (printResults (f ∘ suc)))

main = run (printResults (Data.Nat.Show.show ∘ primes))
