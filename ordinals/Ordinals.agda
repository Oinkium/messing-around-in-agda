module Ordinals where

postulate
  Y : {A : Set} → (A → A) → A

data ℕ : Set where
  zer : ℕ
  suc : ℕ → ℕ

if0 : {A : Set} → ℕ → A → (ℕ → A) → A
if0 zer z s = z
if0 (suc p) z s = s p

O : Set → Set
O = λ A → A → (A → A) → ((ℕ → A) → A) → A

zero : {A : Set} → O A
zero = λ z → λ s → λ l → z

succ : {A : Set} → (O A → O A)
succ = λ α → λ z → λ s → λ l → s (α z s l)

lim : {A : Set} → (ℕ → O A) → O A
lim = λ f → λ z → λ s → λ l → l (λ n → (f n) z s l)

finite : {A : Set} → ℕ → O A
finite = Y(λ f → λ n → if0 n zero (λ p → succ (f p)))

ω : {A : Set} → O A
ω = lim finite

_+_ : {A : Set} → O A → O A → O A
_+_ = λ α → λ β → λ z → λ s → λ l → β (α z s l) s l

ωM : {A : Set} → ℕ → O A
ωM = Y (λ f → λ n → if0 n zero (λ n-1 → (f n-1) + ω))

ω² : {A : Set} → O A
ω² = lim ωM

omegasquared : {A : Set} → O A
omegasquared = ω²

_×_ : {A : Set} → O A → O (O A) → O A
_×_ = λ α → λ β → β zero (λ γ → γ + α) lim

infixr 1 _^_

_^_ : {A : Set} → O (O A) → O (O A) → O A
_^_ = λ α → λ β → β (succ zero) (λ γ → γ × α) lim

ω^ω : {A : Set} → O A
ω^ω = ω ^ ω

test : {A : Set} → O A
test = ω ^ ω ^ ω ^ ω ^ ω ^ ω

postulate
  ⁇ : ℕ

data ℂ : Set where
  OK : ℂ

realize : O ℂ → ℂ
realize = λ α → α OK (λ x → x) (λ f → (f ⁇))
