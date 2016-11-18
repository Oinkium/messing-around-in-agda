{-# OPTIONS  --type-in-type --no-termination-check #-}

module GenericPrompt where
-- in which we provide a generic IO prompt
 
open import Data.String renaming (_++_ to _s++_ ; _==_ to _s==_)
open import Data.List as L renaming (_++_ to _L++_)
open import Data.Maybe
open import Function

{-# IMPORT System.IO #-}
open import Foreign.Haskell
open import FFI.Int
open import FFI.Pair
open import System.IO
open import ParsePrint.PrettyPrint public

putDocLn : Doc → IO Unit
putDocLn = putStrLn' ∘ render

prompt : ∀ {a}(prom : Doc)(parse : String → Maybe a)(cont : a → IO Unit) →
         IO Unit
prompt {a} prom parse cont =
  putDocLn (sep (prom <> text " (or \"quit\") ?" ∷ [])) >>
  getLine' >>= checkQuit
  where
  checkParse : Maybe a → IO Unit
  checkParse nothing  = putDocLn (text "No parse.  Try again.") >>
                        prompt prom parse cont
  checkParse (just a) = cont a

  checkQuit : String → IO Unit
  checkQuit "quit" = return unit
  checkQuit s      = checkParse (parse s)

