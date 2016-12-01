module inductive_graphs where

open import Data.Empty
  renaming (⊥ to ∅)
open import Data.Sum
  renaming (_⊎_ to _⊔_)
open import Data.Product

data ✶ : Set where
  ⋆ : ✶

data bsPlay : Set
vertices : bsPlay → Set
edges : bsPlay → Set
source : (p : bsPlay) → edges p → vertices p
target : (p : bsPlay) → edges p → vertices p

data bsPlay where
  emptyPlay : bsPlay
  addVertex : bsPlay → bsPlay
  addEdge : (p : bsPlay) → vertices p → vertices p → bsPlay

vertices emptyPlay = ∅
vertices (addVertex p) = (vertices p) ⊔ ✶
vertices (addEdge p v w) = vertices p

edges emptyPlay = ∅
edges (addVertex p) = edges p
edges (addEdge p v w) = (edges p) ⊔ ✶

source emptyPlay ()
source (addVertex p) e = inj₁ (source p e)
source (addEdge p v w) = [ (source p) , (λ ⋆ → v) ]

target emptyPlay ()
target (addVertex p) e = inj₁(target p e)
target (addEdge p v w) = [ (target p) , (λ ⋆ → w) ]

