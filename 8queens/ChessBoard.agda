module ChessBoard where

open import Data.Nat
open import Data.Fin
  using (Fin; toℕ; zero; suc; inject₁)
open import Data.Fin.Subset
open import Data.Unit
  using (⊤)
open import Data.Empty
  using (⊥)
open import Data.Vec
open import Data.Sum
  using (_⊎_)
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Sum
open import Induction
import Level

numberOfCells : ℕ
numberOfCells = 64

board : Set
board = (Fin numberOfCells)

finVector : (n : ℕ) → Vec (Fin n) n
finVector zero = []
finVector (suc n) = zero ∷ (Data.Vec.map suc (finVector n))

boardVector : Vec board numberOfCells
boardVector = finVector numberOfCells

boardSubset : Set
boardSubset = Subset numberOfCells

boardWidth : ℕ
boardWidth = 8

row : board → ℕ
row sq = (toℕ sq) div boardWidth

col : board → ℕ
col sq = toℕ ((toℕ sq) mod boardWidth)

attackHorizontal : board → board → Set
attackHorizontal pc sq = row pc ≡ row sq

attackHorizontal? : (pc : board) (sq : board) → Dec (attackHorizontal pc sq)
attackHorizontal? pc sq = row pc ≟ row sq

attackVertical : board → board → Set
attackVertical pc sq = col pc ≡ col sq

attackVertical? : (pc : board) (sq : board) → Dec (attackVertical pc sq)
attackVertical? pc sq = col pc ≟ col sq

attackDiagonal1 : board → board → Set
attackDiagonal1 pc sq = (row pc + col pc) ≡ (row sq + col sq)

attackDiagonal1? : (pc : board) (sq : board) → Dec (attackDiagonal1 pc sq)
attackDiagonal1? pc sq = (row pc + col pc) ≟ (row sq + col sq)

attackDiagonal2 : board → board → Set
attackDiagonal2 pc sq = (row pc + col sq) ≡ (row sq + col pc)

attackDiagonal2? : (pc : board) (sq : board) → Dec (attackDiagonal2 pc sq)
attackDiagonal2? pc sq = (row pc + col sq) ≟ (row sq + col pc)

rookAttack : board → board → Set
rookAttack rk sq = (attackHorizontal rk sq) ⊎ (attackVertical rk sq)

rookAttack? : (rk : board) (sq : board) → Dec (rookAttack rk sq)
rookAttack? rk sq = (attackHorizontal? rk sq) ⊎-dec (attackVertical? rk sq)

queenAttack : board → board → Set
queenAttack qn sq = (attackHorizontal qn sq) ⊎ (attackVertical qn sq) ⊎ (attackDiagonal1 qn sq) ⊎ (attackDiagonal2 qn sq)

queenAttack? : (qn : board) (sq : board) → Dec (queenAttack qn sq)
queenAttack? qn sq = (attackHorizontal? qn sq) ⊎-dec (attackVertical? qn sq) ⊎-dec (attackDiagonal1? qn sq) ⊎-dec (attackDiagonal2? qn sq)

decToSide : {A : Set} → Dec A → Side
decToSide p with p
... | yes _ = inside
... | no  _ = outside

queenAttackSide : board → board → Side
queenAttackSide qn sq = decToSide (queenAttack? qn sq)

safeQueenSquares : board → boardSubset
safeQueenSquares qn = ∁ (map (queenAttackSide qn) boardVector)
