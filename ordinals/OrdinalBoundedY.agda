module OrdinalBoundedY where

-- Divergence

postulate
  Ω : {X : Set} → X

infixr 1 _∘_

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)
