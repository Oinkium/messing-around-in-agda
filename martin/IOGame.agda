{-# OPTIONS --type-in-type #-}

module IOGame where
-- in which we provide functions for printing and parsing games/moves

open import Data.Char
open import Data.Integer using () renaming (+_ to ℕtoℤ)
open import Data.List as L renaming (_++_ to _L++_)
open import Data.String
open import Data.Sum
open import Data.Unit
open import Data.Nat
open import Data.Maybe
open import Data.Product renaming (_,_ to _,'_)
import Data.Integer

open import Foreign.Haskell
open import Function

open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)

open import ParsePrint.PrettyPrint as PP

open import ParserCore

-- Printing Moves

ErrorMsg = Doc

prMovEnc : MovEnc → Doc
prMovEnc nil     = text "nil" 
prMovEnc one     = text "one"
prMovEnc (i ⊹ j) = PP.parens (prMovEnc i <> text " + " <> prMovEnc j)
prMovEnc (ℕ× i)  = text "ℕ×" <> PP.parens (prMovEnc i)

primitive
    primStringToList : String → List Char

shownat = primStringToList ∘ PP.primShowInteger ∘ PP.primNatToInteger

prMov : (i : MovEnc) → T i → Doc
prMov i x =  text (fromList (prMov' i x))
  where
  prMov' : (i : MovEnc) → T i → List Char
  prMov' nil     ()
  prMov' one     _           = '0' ∷ []
  prMov' (i ⊹ j) (inj₁ x)    = 'L' ∷ prMov' i x
  prMov' (i ⊹ j) (inj₂ y)    = 'R' ∷ prMov' j y
  prMov' (ℕ× i)   m          = shownat (proj₁ m) L++ prMov' i (proj₂ m) 

listMovEnc : (ι : MovEnc) → List (T ι)
listMovEnc nil     = []
listMovEnc one     = tt ∷ []
listMovEnc (ι ⊹ κ) = L.map inj₁ (listMovEnc ι) L++
                       L.map inj₂ (listMovEnc κ)
listMovEnc (ℕ× ι) = L.map (λ x → (0 ,' x)) (listMovEnc ι) L++
                       L.map (λ x → (1 ,' x)) (listMovEnc ι)
              -- only give a few examples

descMoves : MovEnc → Doc
descMoves ι = aux (listMovEnc ι) zero
  where aux : List (T ι) → ℕ → Doc
        aux []       _ = text ""
        aux (x ∷ []) n = prMov ι x
        aux (x ∷ xs) n = prMov ι x <> text ", "
                         <> aux xs (suc n)

pickMove : (ι : MovEnc) → ℕ → Maybe (T ι)
pickMove ι = nth (listMovEnc ι)
  where nth : ∀ {A} → List A → ℕ → Maybe A
        nth []        _       = nothing
        nth (x ∷ xs)  zero    = just x
        nth (x ∷ xs) (suc n) = nth xs n

-- Printing Games

prPol : Pol → Doc
prPol + = text "+"
prPol - = text "-"

prGame : Pol → Game → Doc
prGame p (gam {a} f) = 
  prPol p <> PP.char ':' <> prMovEnc a $$
  nest (ℕtoℤ 2)
   (vcat (L.map (λ i → prGame (¬ p) (f i)) (listMovEnc a)))

-- Parsing Moves

pMov : ∀ (ι : MovEnc) → ReadP (T ι)
pMov nil     = pfail
pMov one     = lexchar '0' >> return tt
pMov (ι ⊹ κ) = (lexchar 'L' >> inj₁ <$> pMov ι) +++
               (lexchar 'R' >> inj₂ <$> pMov κ)
pMov (ℕ× ι)  = lexnum >>= (λ n → (λ x → (n ,' x)) <$> pMov ι)


