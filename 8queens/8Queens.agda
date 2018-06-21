module 8Queens where

open import Data.Nat
open import Data.Fin
open import Data.Fin.Subset
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Unary
  using ()
import Level

open import ChessBoard
  using (board; boardSubset; safeQueenSquares)

data nQueens : ℕ → Set
legalPositions : {n : ℕ} → nQueens n → boardSubset

data nQueens where
  emptyBoard : nQueens 0
  placeQueen : {n : ℕ} (p : nQueens n) (sq : board) → {lg : sq ∈ legalPositions p} → nQueens (suc n)

legalPositions emptyBoard = ⊤
legalPositions (placeQueen p sq) = (legalPositions p) ∩ (safeQueenSquares sq)

isSolution : (n : ℕ) → Dec (nQueens n)
isSolution 0 = yes emptyBoard
isSolution (suc n) = {!!}
