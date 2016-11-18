module FFI.Pair where

-- non dependent product for FFI

infixr 2 _×'_
infixr 4 _,'_

data _×'_(A B : Set) : Set where
  _,'_ : A -> B -> A ×' B

{-# COMPILED_DATA _×'_ (,) (,) #-}

uncurry' : ∀ {A B C : Set} → (A → B → C) → (A ×' B → C)
uncurry' f (a ,' b) = f a b

