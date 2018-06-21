module OrdinalY where

open import Data.Sum
  using (_⊎_; inj₁; inj₂)

-- Our base types

data ℕ : Set where
  zer : ℕ
  suc : ℕ → ℕ

data ℂ : Set where
  OK : ℂ

-- Nondeterministic choice

postulate
  ⁇ : ℕ

-- Divergence
postulate
  Ω : {T : Set} → T

-- Basic definition of (Church encodings of) ordinals

O : Set → Set
O = λ X → X → (X → X) → ((ℕ → X) → X) → X

zero : {X : Set} → O X
zero = λ z s l → z

succ : {X : Set} → O X → O X
succ = λ α z s l → s (α z s l)

lim : {X : Set} → ((ℕ → O X) → O X)
lim = λ f z s l → l (λ n → (f n) z s l)

-- Ordinal arithmetic

_+_ : {X : Set} → O X → O X → O X
_+_ = λ α β z s l → β (α z s l) s l

_×_ : {X : Set} → O X → O (O X) → O X
_×_ = λ α β → β zero (λ γ → γ + α) lim

_^_ : {X : Set} → O (O X) → O (O X) → O X
_^_ = λ α β → β (succ zero) (λ γ → γ × α) lim

-- A nondeterministic predecessor function:
--   pred 0 = Ω
--   pred (succ α) = α
--   pred (lim αₙ) = αₘ, where m is chosen nondeterministically

pred : {X : Set} → O (O X) → O X
pred = λ α → α Ω (λ x → x) (λ f → f ⁇)

-- Realization of ordinals over ℂ

realize : O ℂ → ℂ
realize = λ α → α OK (λ x → x) (λ f → f ⁇)

-- An ordinal type that allows uniform definitions of arithmetic functions

Oⁿ : ℕ → Set → Set
Oⁿ zer X = X
Oⁿ (suc n) X = O (Oⁿ n X)

O' : Set → Set
O' = λ X → (n : ℕ) → O (Oⁿ n X)

-- Basic operations

zero' : {X : Set} → O' X
zero' = λ n → zero

succ' : {X : Set} → O' X → O' X
succ' α = λ n → succ (α n)

lim' : {X : Set} → (ℕ → O' X) → O' X
lim' f = λ n → lim (λ m → f m n)

-- Arithmetic for these new types

_+'_ : {X : Set} → O' X → O' X → O' X
α  +' β = λ n → (α n) + (β n)

_×'_ : {X : Set} → O' X → O' X → O' X
α ×' β = λ n → (α n) × (β (suc n))

_^'_ : {X : Set} → O' X → O' X → O' X
α ^' β = λ n → (α (suc n)) ^ (β (suc n))

-- Nondeterministic predecessor

pred' : {X : Set} → O' X → O' X
pred' α = λ n → pred (α (suc n))

-- Coercion from O' to O

O'↦O : {X : Set} → O' X → O X
O'↦O α = α zer

-- Ordinal indexed recursion combinators

Y : {X T : Set} → O' X → (T → T) → T
Y α f = f(Y (pred' α) f)

-- Defining some ordinals

finite : {X : Set} → ℕ → O' X
finite zer = zero'
finite (suc n) = succ' (finite n)

ω : {X : Set} → O' X
ω = lim' finite

-- Even numbers
evenHelper : (ℕ → ℕ) → ℕ → ℕ
evenHelper f zer = zer
evenHelper f (suc n) = suc (suc (f n))

even : ℕ → ℕ
even = Y zero' evenHelper
