module Bracketing where

open import Data.Integer
open import Data.Bool
open import Data.List

open import Relation.Binary.PropositionalEquality

data bracket : Set where
  [ : bracket
  ] : bracket

isWellBracketed-helper : ℤ → List bracket → Bool
isWellBracketed-helper (-[1+ n ]) _ = false
isWellBracketed-helper (+ n) [] = true
isWellBracketed-helper (+ n) (b ∷ bs) with b
... | [ = isWellBracketed-helper (+ n + + 1) bs
... | ] = isWellBracketed-helper (+ n - + 1) bs

isWellBracketed : List bracket → Bool
isWellBracketed bs = isWellBracketed-helper (+ 0) bs

invert : bracket → bracket
invert [ = ]
invert ] = [

invertList : List bracket → List bracket
invertList bs = map invert (reverse bs)

private
  test1 : isWellBracketed ([ ∷ ] ∷ []) ≡ true
  test1 = refl

  test2 : isWellBracketed ([ ∷ ] ∷ [ ∷ ] ∷ []) ≡ true
  test2 = refl

  test3 : isWellBracketed ([ ∷ ] ∷ ] ∷ [ ∷ []) ≡ false
  test3 = refl
   
  test4 : invertList ([ ∷ [ ∷ ] ∷ []) ≡ [ ∷ ] ∷ ] ∷ []
  test4 = refl
