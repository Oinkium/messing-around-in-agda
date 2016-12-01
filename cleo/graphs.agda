module graphs where

open import Agda.Builtin.Nat
  renaming (Nat to ℕ)

open import Agda.Builtin.Bool

open import Data.Product
open import Data.Sum
  renaming (_⊎_ to _⊔_)
open import Relation.Binary.PropositionalEquality

data ✶ : Set where
  sing : ✶

record Graph : Set₁ where
  field
    vertices : Set
    edges : Set
    source : edges → vertices
    target : edges → vertices

vertices : Graph → Set
vertices G = Graph.vertices G

edges : Graph → Set
edges G = Graph.edges G

source : (G : Graph) → (e : edges G) → vertices G
source G e = Graph.source G e

target : (G : Graph) → (e : edges G) → vertices G
target G e = Graph.target G e

addVertex : Graph → Graph
addVertex G = record { vertices = (vertices G) ⊔ ✶ ; edges = edges G ; source = λ e → inj₁ (source G e) ; target = λ e → inj₁ (target G e) }

addEdge : (G : Graph) → (vertices G) → (vertices G) → Graph
addEdge G v w = record { vertices = vertices G ; edges = edges G ⊔ ✶ ; source = [_,_] (source G) (λ _ → v) ; target = [_,_] (target G) (λ _ → w) }

-- Set of edges between two vertices.
_│_⟿_ : (G : Graph) (v : vertices G) → (w : vertices G) → Set
G │ v ⟿ w = Σ (edges G) (λ e → ((source G e) ≡ v) × ((target G e) ≡ w))

-- Our graphs are always undirected, so the edge relation is
-- populated if there is an edge going in either direction.
-- Accordingly, we represent the edge relation between vertices
-- v and w as the disjoint union of the set of edges from v to
-- w and the set of edges from w to v.
_│_∼_ : (G : Graph) → (v : vertices G) → (w : vertices G) → Set
G │ v ∼ w = (G │ v ⟿ w) ⊔ (G │ w ⟿ v)
