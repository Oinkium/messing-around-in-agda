{-# OPTIONS  --type-in-type --no-termination-check #-}

module Interaction where
-- top level module for interacting with AgdaWS

open import Data.Unit
open import Function
open import Data.Product
open import Data.Nat
open import Data.List
open import Data.Bool

{-# IMPORT System.IO #-}
open import System.IO
open import Foreign.Haskell

open import WS-Syn
open import WS-Sem
open import IOWS
open import WS-Annot
open import WS-Exp
open import WS-Comp
open import WS-Tex
open import WS-SCIL-Consts
open import RunStrategy
open import ParsePrintLoop
open import GenericPrompt

-- Take a proof, and run the semantics of that proof

runprf : ∀ {p}{Γ : Seq p} → ⊢ Γ → IO Unit
runprf { - } {Γ} prf = Ask  ⟦ prf ⟧⊢ (anotate $ Γ F) (prFml ∘ proj₂)
runprf { + } {Γ} prf = Tell ⟦ prf ⟧⊢ (anotate $ Γ F) (prFml ∘ proj₂)

-- Ask for a proof at the terminal, parse it and run the semantics of
-- that proof:

askRunPrf : IO Unit
askRunPrf = prompt (text "Proof") parsePrf cont where
  cont : Prf → IO Unit
  cont (Γ ⊣: prf) =
    putDocLn (sep (text "Proof parsed: " ∷ prPrf (Γ ⊣: prf) ∷ []) $$
              text "-------------------------------------------" ) >>
    runprf prf

-- Main functions we have access to:

-- We can ask for a sequent and print out the game tree:
test1 = askShowSeq

-- A cell that can be written to / read 3 times
--    (can be replaced with other examples from WS-Exp)

3cell = cell 3 true

-- We can run it:
test2 = runprf 3cell

-- Print it out in latex:
test3 = putDocLn (prf2tex 3cell)

-- Print out the game tree:
test4 = putDocLn (prAnnFml (! 3 Fvar))

-- Normalise it:
n3cell = nbe 3cell

-- Run the normalised version (same behaviour):
test5 = runprf n3cell

-- Latex out the normalised version:

test6 = putDocLn (prf2tex n3cell)

test7 = runprf notPrf

main = hSetBuffering stdout NoBuffering >>
          test2
