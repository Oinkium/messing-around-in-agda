module ordinals where

-- Natural numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

-- Ordinal type
data Ordinal : Set where
  zer : Ordinal
  suc : Ordinal -> Ordinal
  lim : (ℕ -> Ordinal) -> Ordinal

FiniteOrdinal : ℕ -> Ordinal
FiniteOrdinal zero = zer
FiniteOrdinal (succ N) = suc (FiniteOrdinal N)

ω : Ordinal
ω = lim FiniteOrdinal

ωM+N : ℕ -> (ℕ -> Ordinal)
ωM+N zero zero = zer
ωM+N m (succ N) = suc (ωM+N m N)
ωM+N (succ M) zero = lim(ωM+N M)

ω² : Ordinal
ω² = lim(λ m -> (ωM+N m zero))

-- Constructing higher ordinals up to ε₀

Ordinal' : Set
Ordinal' = Ordinal -> Ordinal

Reduce : Ordinal' -> Ordinal
Reduce f = f(zer)

zer' : Ordinal'
zer' a = a

suc' : Ordinal' -> Ordinal'
suc' f a = suc(f a)

lim' : (ℕ -> Ordinal') -> Ordinal'
lim' f a = lim(λ n -> f n a)

one' : Ordinal'
one' = suc' zer'

add' : Ordinal' -> (Ordinal' -> Ordinal')
add' f g = λ a -> f (g a)

XN' : Ordinal' -> (ℕ -> Ordinal')
XN' X zero = zer'
XN' X (succ N) = add' X (XN' X N)

Xω' : Ordinal' -> Ordinal'
Xω' X = lim'(λ n -> XN' X n)

ωᴺ' : ℕ -> Ordinal'
ωᴺ' zero = one'
ωᴺ' (succ N) = Xω' (ωᴺ' N)

ωᴺ : ℕ -> Ordinal
ωᴺ n = Reduce (ωᴺ' n)

ω^ω : Ordinal
ω^ω = lim(ωᴺ)
