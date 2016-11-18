{-# OPTIONS  --type-in-type --no-termination-check #-}

module ParsePrintLoop where
-- in which we program a parse/print loop, where the user inputs the
-- formula and the program prints out the corresponding (annotated)
-- game

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Integer using () renaming (+_ to ℕtoℤ)
open import Data.List as L renaming (_++_ to _L++_)
open import Data.String renaming (_++_ to _s++_ ; _==_ to _s==_)
open import Data.Sum
open import Data.Unit
open import Data.Product renaming (_,_ to _,'_)

open import Foreign.Haskell
open import System.IO
open import ParsePrint.PrettyPrint as PP
open import ParserCore as PC
open import GenericPrompt

open import Game
open import IOGame
open import WS-Syn
open import IOWS
open import WS-Annot

-- Printing annotated games:

prAnGame : ∀ {G} → Annotation G (λ _ → PolFml) → Doc
prAnGame {G} (ν (p ,' A) f) =
  prPol p <> PP.char ':' <> prFml A $$
  nest (ℕtoℤ 2) 
    (vcat (L.map (λ i → prAnGame (f i)) (listMovEnc (mvEnc G))))

prAnnFml : ∀{pol} → Fml pol  → Doc
prAnnFml = prAnGame ∘ anotate

askShowFml : IO Unit
askShowFml = prompt (text "Fml") parseFml cont where
  cont : PolFml → IO Unit
  cont (p ,' A) = putDocLn ((prFml A) $$
                            text "----" $$
                            prAnnFml A
                          )

askShowSeq : IO Unit
askShowSeq = prompt (text "Seq ") parseSeq cont where
  cont : PolSeq → IO Unit
  cont (p ,' Γ) = putDocLn (text "--------------------" $$ prSeq Γ)
