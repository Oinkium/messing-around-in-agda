open import Algebra

module SemiRingSolver {c ℓ} {A : Semiring c ℓ} where

open Semiring A

open import Data.Nat
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality

data Expression : Set where
    con : ℕ → Expression
    _:+_ : Expression → Expression → Expression
    _:*_ : Expression → Expression → Expression

data Equation : Set where
    _:=_ : Expression → Expression → Equation

EqNFree : ℕ → Set
EqNFree zero = Equation
EqNFree (suc n) = Expression → (EqNFree n)

realizeExpression : Expression → Carrier
realizeExpression (con zero) = 0#
realizeExpression (con (suc n)) = 1# + (realizeExpression (con n))
realizeExpression (e :+ f) = (realizeExpression e) + (realizeExpression f)
realizeExpression (e :* f) = (realizeExpression e) * (realizeExpression f)

RealizeEquation : Equation → Set c
RealizeEquation (f := g) = (realizeExpression f) ≡ (realizeExpression g)

Realize : ∀ n → EqNFree n → Set c
Realize zero e = RealizeEquation e
Realize (suc n) f = ∀ x → (Realize n (f x))

solve : (n : ℕ) → (e : EqNFree n) → Realize n e
solve = {!!}
