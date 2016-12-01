module mltt where

-- Here are some Martin-Löf type theory style things.

-- Propositional equality

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Dependent pair type Σ

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → (B a) → Σ A B

pr₁ : {A : Set} {B : A → Set} → Σ A B → A
pr₁ (a , x) = a

pr₂ : {A : Set} {B : A → Set} → (p : Σ A B) → B (pr₁ p)
pr₂ (a , x) = x

-- Product type (defined in terms of the Σ type

_×_ : (A : Set) (B : Set) → Set
A × B = Σ A (λ a → B)



