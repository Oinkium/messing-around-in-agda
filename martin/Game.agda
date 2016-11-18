module Game where
-- in which we formalise some Game Semantics in Agda

-- Core game semantics:
open import Game-Core public

-- Standard copycat strategies:
open import Game-Morphs public
open import Game-Strats public

-- Annotations on games:

-- For example, Annotation G (λ _ → String) would be a game where each
-- node is annotated by a string. We allow the annotation type to
-- depend on the current subgame, for integration with formulas.

data Annotation (G : Game) (A : Game → Set) : Set where
  ν : A G → ((i : Mov G) → Annotation (G ▸ i) A) → Annotation G A
