module LookAndSay where

open import Function
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Bool
  using (Bool ; true ; false ; if_then_else_ )
open import Relation.Nullary using (¬_; Dec; yes; no)

_∷_ : ∀ {a} {A : Set a} {m} → A → (Fin m → A) → (Fin (suc m) → A)
(a ∷ f) zero = a
(a ∷ f) (suc n) = f n

-- if_then-apply_ : ∀ {a} {A : Set a} → (A → Bool)
-- modifyInPlace : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → A → (B → B)

lookAndSay₁ : ∃ (λ m → Fin m → ℕ) → ℕ
lookAndSay₂ : (p : ∃ (λ m → Fin m → ℕ)) → Fin (lookAndSay₁ p) → ℕ
lookAndSay : ∃ (λ m → Fin m → ℕ) → ∃ (λ n → Fin n → ℕ)

lookAndSay₁ (zero , f) = zero
lookAndSay₁ (suc zero , f) = suc (suc zero)
lookAndSay₁ (suc (suc n) , f) with (f zero ≟ f (suc zero))
... | yes eq = lookAndSay₁ (suc n , f ∘ suc)
... | no neq = suc (lookAndSay₁ (suc n , f ∘ suc))

lookAndSay₂ (zero , f) = f
lookAndSay₂ (suc zero , f) = 1 ∷ f
lookAndSay₂ (suc (suc n) , f) with (f zero ≟ f (suc zero))
... | yes eq = λ {zero → suc (f zero)
                 ; (suc m) → lookAndSay₂ (suc n , f ∘ suc) (suc m)}
... | no neq = λ {zero → 1
                 ; (suc zero) → (f zero)
                 ; (suc (suc m)) → lookAndSay₂ (suc n , f ∘ suc) m}

lookAndSay p = (lookAndSay₁ p , lookAndSay₂ p)
