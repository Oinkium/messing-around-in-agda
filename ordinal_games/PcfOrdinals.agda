module PcfOrdinals where

postulate
  Y : {A : Set} → (A → A) → A

data ℕ : Set where
  zer : ℕ
  succ : ℕ → ℕ

if0 : {A : Set} → ℕ → A → (ℕ → A) → A
if0 zer z f = z
if0 (succ n) z f = f n

data ℂ : Set where
  OK : ℂ

Ord : Set
Ord = ℂ → (ℂ → ℂ) → ((ℕ → ℂ) → ℂ) → ℂ

zero : Ord
zero = λ z → λ s → λ l → z

suc : Ord → Ord
suc = λ o → λ z → λ s → λ l → s (o z s l)

lim : (ℕ → Ord) → Ord
lim = λ os → λ z → λ s → λ l → l (λ n → os n z s l)

finite : ℕ → Ord
finite = Y (λ f → λ n → if0 n zero (λ p → suc (f p)))

ω : Ord
ω = lim finite

ωm+n : ℕ → ℕ → Ord
ωm+n = Y (λ f → λ m → λ n → (if0 m (finite n) (λ p → (if0 n (lim (λ k → f p k)) (λ q → (suc (f p q)))))))

ω² : Ord
ω² = lim (λ m → ωm+n m zer)

ω²
