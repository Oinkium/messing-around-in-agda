module higher_recursive_ordinals where

-- Natural numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

-- General purpose ordinal type
Ordinal : Set -> Set
Ordinal X = X -> ((X -> X) -> (((ℕ -> X) -> X) -> X))

zer : {X : Set} -> Ordinal X
zer z s l = z

suc : {X : Set} -> (Ordinal X -> Ordinal X)
suc a z s l = s(a z s l)

lim : {X : Set} -> (ℕ -> Ordinal X) -> Ordinal X
lim f z s l = l (λ n -> (f n) z s l)

FiniteOrdinal : {X : Set} -> ℕ -> Ordinal X
FiniteOrdinal zero = zer
FiniteOrdinal (succ n) = suc(FiniteOrdinal n)

ω : {X : Set} -> Ordinal X
ω = lim (FiniteOrdinal)

ωM+N : {X : Set} -> (ℕ -> (ℕ -> Ordinal X))
ωM+N zero zero = zer
ωM+N m (succ N) = suc(ωM+N m N)
ωM+N (succ M) zero = lim(ωM+N M)

ω² : {X : Set} -> Ordinal X
ω² = lim(λ m -> ωM+N m zero)

-- Concrete implementation as functions ℕ -> ℕ
-- We use the Hamilton hierarchy:
--  - f₀(n) = n + 1
--  - fₐ₊₁(n) = fₐ(n) + 1
--  If l = limₙ aₙ then
--    fₗ(n) = fₐₙ(n)

NatFunc : Set
NatFunc = ℕ -> ℕ

HamiltonZero : NatFunc
HamiltonZero n = succ n

HamiltonSucc : NatFunc -> NatFunc
HamiltonSucc f n = succ(f n)

HamiltonLimit : (ℕ -> NatFunc) -> NatFunc
HamiltonLimit s n = s n n

-- Concrete implementation as sets.
-- We use the hierarchy where:
--  - S₀ = ω
--  - Sₐ₊₁ = 𝒫(Sₐ)
--  If l = limₙ aₙ then
--    Sₗ = ⋃ₐₙ Sₐₙ

-- Empty set
data ∅ : Set where

--Boolean type
data Bool : Set where
  ⊤ : Bool
  ⊥ : Bool

-- Power set
𝒫 : Set -> Set
𝒫 A = A -> Bool

-- (Disjoint) union of sets
data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) -> B a -> Σ A B

-- Defining the hierarchy
SetZero : Set
SetZero = ℕ

SetSucc : Set -> Set
SetSucc A = 𝒫 A

SetLimit : (ℕ -> Set) -> Set
SetLimit s = Σ ℕ s

-- Higher recursive types
Ordinal' : Set -> Set
Ordinal' X = Ordinal X -> Ordinal X

zer' : {X : Set} -> Ordinal' X
zer' f = f

suc' : {X : Set} -> (Ordinal' X -> Ordinal' X)
suc' f a = suc(f a)

lim' : {X : Set} -> ((ℕ -> Ordinal' X) -> Ordinal' X)
lim' s a = lim(λ n -> (s n a))

-- For fun, we print out some values.

-- We write some silly code for printing out natural numbers
open import Agda.Builtin.String

PrintNumber : ℕ -> String
PrintNumber zero = ""
PrintNumber (succ N) = primStringAppend (PrintNumber N) "|"

open import IO

Hamiltonω² : ℕ -> ℕ
Hamiltonω² = ω² HamiltonZero HamiltonSucc HamiltonLimit

main = run (putStrLn (PrintNumber (Hamiltonω² (succ (succ zero)))))
