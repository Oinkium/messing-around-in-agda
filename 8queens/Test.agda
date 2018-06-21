module Test where

open import Data.Nat

-- Declaration.
data Vec (A : Set) : ℕ → Set  -- Note the absence of ‘where’.

-- Definition.
data Vec A where
  []   : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- Declaration.
record Sigma (A : Set) (B : A → Set) : Set

-- Definition.
record Sigma A B where
  constructor _,_
  field fst : A
        snd : B fst
