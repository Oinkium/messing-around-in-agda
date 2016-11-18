module Index where

-- Agda formalisation of the logic WS
--   as introduced in "A Logic of Sequentiality", CSL 2010
--                 by Martin Churchill and Jim Laird

-- Agda formalisation by Martin Churchill and Makoto Takeyama.
 
-- Section 1 : Foundations

-- Formalisation of game semantics in Agda
open import Game

-- Formalisation of the logic WS
open import WS-Syn

-- Formalisation of the game semantics of WS
open import WS-Sem

-- Reification of strategies as core proofs (and thus normalisation of
-- proofs to core proofs, via the semantics)
open import WS-Comp

-- Cut elimination procedure for core proofs
open import WS-Cut

-- Examples of WS proofs, including bounded exponentials, coroutines,
-- ground store...
open import WS-Exp

-- A Finitary Language and its game semantics, via WS
open import FinLang

-- Section 2 : Interaction

-- Converts a formula into an *annotated* game, where moves are
-- annotated with the corresponding subformulas
open import WS-Annot

-- Parsing and Printing Games and Formulas
open import IOWS
open import IOGame

-- A module to "run" a strategy, where the computer plays the role of
-- Player and the user is invited to play the role of Opponent
open import RunStrategy

-- A module where the user types in a formula F and the program prints
-- the corresponding annotated game
open import ParsePrintLoop

-- A module to turn proofs in WS into Latex
open import WS-Tex

-- Some Examples
open import Interaction

-- Infinite versions!

open import Game-CoreInf
