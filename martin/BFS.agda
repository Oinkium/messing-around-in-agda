module BFS where

open import Data.Fin
open import Data.Fin.Props as FP
open import Data.Function
open import Data.Unit
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.List as L
-- open import Data.Vec as Vec renaming (_++_ to _++-vec_)
open import Relation.Nullary
open import Relation.Nullary.Product
-- open import Relation.Unary renaming (U to UniversalPred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Empty

¬-dec : ∀{P} → Dec P → Dec(¬ P)
¬-dec (yes p) = no (λ np → np p)
¬-dec (no np) = yes np

module WithFinGraph
       (N : ℕ)
       (S : Fin N → List (Fin N))
       where
  Node = Fin N
  Nodes = List Node

  infix 4 _∉_

  _∉_ : (y : Node)(xs : Nodes) → Set
  y ∉ []     = ⊤
  y ∉ x ∷ xs = y ≢ x × y ∉ xs

  _∉?_ : (y : Node)(xs : Nodes) → Dec (y ∉ xs)
  y ∉? [] = yes tt
  y ∉? (x ∷ xs) = ¬-dec (FP._≟_ y x) ×-dec (y ∉? xs)

  {-
  bfs' : (max : ℕ)(to-visit visited : Nodes)→ Nodes
  bfs' 0       _        us  = us
  bfs' (suc n) []       us  = us
  bfs' (suc n) (v ∷ vs) us  with v ∉? us
  ...                         | yes v∉us = bfs' n (vs ++ S v) (v ∷ us)
  ...                         | no  v∈us = bfs' (suc n) vs us
  -}

  open import Induction
  open import Induction.Nat as IN
  open import Induction.Lexicographic renaming ([_⊗_] to ⟨_⊗_⟩)

  LRec : RecStruct Nodes
  LRec P []       = ⊤
  LRec P (x ∷ xs) = P xs

  Lrec-builder : RecursorBuilder LRec
  Lrec-builder P f [] = tt
  Lrec-builder P f (x ∷ xs) = f xs (Lrec-builder P f xs)

  bfs : ℕ × Nodes × Nodes → Nodes
  bfs = (build ⟨ IN.rec-builder ⊗ ⟨ Lrec-builder ⊗ Lrec-builder ⟩ ⟩) P f
    where
    P : ℕ × Nodes × Nodes → Set
    P _ = Nodes
    f : ∀ p → (IN.Rec ⊗ (LRec ⊗ LRec)) P p → P p
    f (0     , _      , us) _ = us
    f (suc n , []     , us) _ = us
    f (suc n , v ∷ vs , us) ((x , f[sn]vs) , fn) = if' (v ∉? us)
      where if' : Dec(v ∉ us) → Nodes
            if' (yes v∉us) = fn (vs ++ S v , v ∷ us)
            if' (no  v∈us) = f[sn]vs us

  S' : Node × Nodes → List(Node × Nodes)
  S' (x , p) = L.map (\ y → (y , x ∷ p)) (S x)
  
  {-
  bfs2' : (max : ℕ)(to-visit visited : List(Node × Nodes)) → List(Node × Nodes)
  bfs2' 0       _        us  = us
  bfs2' (suc n) []       us  = us
  bfs2' (suc n) ((v , p) ∷ vs) us  with v ∉? L.map proj₁ us
  ... | yes v∉us = bfs2' n (vs ++ S' (v , p)) ((v , p)∷ us)
  ... | no  v∈us = bfs2' (suc n) vs us
  -}
