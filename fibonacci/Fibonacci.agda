module Fibonacci where

open import Data.Nat
  using (ℕ; zero; suc; _+_)
open import Data.Nat.Show
  using (show)

fib-helper : ℕ → ℕ → ℕ → ℕ
fib-helper 0 v p = p
fib-helper 1 v p = v
fib-helper (suc (suc t)) v p = fib-helper (suc t) (v + p) v

fib : ℕ → ℕ
fib t = fib-helper t 1 0

2ⁿ : ℕ → ℕ
2ⁿ zero = 1
2ⁿ (suc n) = prev + prev
  where prev = 2ⁿ n

open import IO
  using (run; putStrLn)

main = run (putStrLn (show (2ⁿ 100)))
