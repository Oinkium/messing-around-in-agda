{-# OPTIONS  --type-in-type #-}

module ParserCore where
-- in which we define some basic parsing functions

open import Data.Maybe
open import Data.Product renaming (_,_ to _,'_)
open import Data.List as L renaming (_++_ to _L++_)
open import Function
open import Data.String
open import Data.Char
open import Data.Nat

open import Foreign.Haskell
open import FFI.Pair
open import Category.Monad

open import ParsePrint.ReadP as RP public

open module dummy = RawMonadPlus monadR public
  renaming (_⊗_ to _R⊗_)

lexeme : ∀ {a} → ReadP a → ReadP a
lexeme p = p >>= λ a → skipSpaces >> return a

lexchar = lexeme ∘ RP.char
lexstr  = lexeme ∘ RP.string

lexcount : Char → ReadP ℕ
lexcount c = RP.many (lexchar c) >>= (λ x → return (L.length x))

pTop : ∀ {a} → ReadP a → ReadP a
pTop p = skipSpaces >> p >>= λ a → eof >> return a

Res_to_Maybe : ∀ {a} → Res a → Maybe a
Res_to_Maybe ((A ,' []) ∷ _) = just A
Res_to_Maybe _               = nothing

parseTop : ∀ {a} → ReadP a → String → Maybe a
parseTop p s = Res_to_Maybe $ readP_to_S (pTop p) (toList s)

parens : ∀ {a} → ReadP a → ReadP a
parens = between (lexchar '(') (lexchar ')')

binl  : ∀ {a} → ReadP a → Char → (a → a → a) → ReadP a
binl  p c f = chainl1 p (lexchar c >> return f)

binl' : ∀ {a b} → ReadP a → Char → (a → b → a) → ReadP b → ReadP a
binl' p c f q = p >>= λ P → foldl f P <$> many (lexchar c >> q)

private
  primitive
    primStringToList : String → List Char
    primCharToNat : Char → ℕ

open import Data.Nat
pDigit : ReadP ℕ
pDigit = choice (L.map char (primStringToList "0123456789")) >>= λ c →
         return (primCharToNat c {- ?  primCharToNat '0' -} )

pNum : ReadP ℕ
pNum = L.foldl (λ n r → _+_ (n * 10) r) 0 <$> many1 pDigit

lexnum = lexeme pNum