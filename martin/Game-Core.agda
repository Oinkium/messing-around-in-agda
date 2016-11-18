module Game-Core where
-- in which we formalise the fundamentals of Game Semantics in Agda

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_+_ to _+'_)

-- Games

-- At each level of the game, we have a set of possible moves. For
-- cardinality reasons, it is useful to restrict that set to one of
-- the following forms:

infixr 8 _⊹_
data MovEnc : Set where
  nil : MovEnc
  one : MovEnc
  _⊹_ : MovEnc → MovEnc → MovEnc
  ℕ× : MovEnc → MovEnc

-- where each constructor represents a set in the following manner:

T : MovEnc → Set
T nil      = ⊥
T one      = ⊤ 
T (x ⊹ y)  = T x ⊎ T y
T (ℕ× m)   = ℕ × T m 

-- So a game consists of an (encoded) set of moves, and for each move
-- a corresponding "rest of the game":

data Game : Set where
  gam : {ι : MovEnc} → (T ι → Game) → Game

mvEnc : Game → MovEnc
mvEnc (gam {a} f) = a

Mov : Game → Set
Mov G = T (mvEnc G)

infix 10 _▸_
_▸_ : (G : Game) → Mov G → Game
(gam {ι} f) ▸ i = f i

-- Constructions on Games

I : Game
I = gam {nil} ⊥-elim

_×'_ : Game → Game → Game
gam {i} f ×' gam {j} g = gam {i ⊹ j} [ f , g ]

ω× : Game → Game
ω× (gam {i} f) = gam {ℕ× i} (λ x →  f (proj₂ x))

infix 14 _⊗_
infix 12 _⊸_ _⊸̂_

mutual
  _⊸_ : Game → Game → Game
  G ⊸ (gam {i} f) = gam {i} (λ i' → f i' ⊗ G)

  _⊘_ : Game → Game → Game
  (gam {i} f) ⊘ G = gam {i} (λ i' → G ⊸ f i')

  _⊗_ : Game → Game → Game
  G ⊗ H = (G ⊘ H) ×' (H ⊘ G)

o : Game
o = gam {one} (λ _ → I)

_⊸o : Game → Game
G ⊸o = gam {one} (λ tt → G)

-- ⊸̂ represents a strict function space:
_⊸̂_ : Game → Game → Game
G ⊸̂ (gam {i} f) = gam {i} (λ i' → G ⊘ f i')

-- ⊸c represents copycat-shaped function space
_⊸c_ : Game → Game → Game
G ⊸c (gam {i} f) = gam {i} (λ i' → G ⊘c f i')
  where _⊘c_ : Game → Game → Game
        (gam {i} f) ⊘c G = gam {i} (λ i' → G ⊸c f i')

-- Strategies

-- We now need to consider games of a particular polarity.

open import Data.Bool public
   renaming (true to -  ; false to +;
             Bool to Pol; not   to ¬;
             T to IsTrue)

-- If we consider negative games, the top (1st) level represent the
-- O-positions, and then on even levels we have P-positions and odd
-- levels O-positions. In which case a (P)-strategy for a game M is
-- given as a term of type Strat - M, where:

data Strat : Pol → Game → Set where
  pos : ∀ {G} → (i : Mov G) → Strat - (G ▸ i) → Strat + G
  neg : ∀ {G} → ((i : Mov G) → Strat + (G ▸ i)) → Strat - G

-- If we consider a positive game Q, a P-strategy on Q is given by a
-- term of type Strat + Q.

-- Game morphisms

-- Our mediating morphisms / isos are going to be defined as
-- copycat-shaped strategies on A ⊸ B --- or strategies on A ⊸c B. But
-- we're going to be working with a lot of these, and the notion of
-- such a strategy can be given a simpler form:

infix 8 _≲_
data _≲_ : Game → Game → Set where
  sim : ∀ {A B} →
        (h : Mov B → Mov A) →
        ((i' : Mov B) → (B ▸ i') ≲ (A ▸ (h i'))) →
        A ≲ B

id≲ : ∀ {G} → G ≲ G
id≲ {gam f} = sim id (λ i → id≲ {f i})

infixl 8 _≲∘≲_

_≲∘≲_ : ∀ {A B C} → B ≲ C → A ≲ B → A ≲ C
(sim f f') ≲∘≲ (sim g g') = sim (g ∘ f) (λ x → g' (f x) ≲∘≲ (f' x))

-- We bundle two-way copycat strategies into a ≈ structure.
-- This is how we represent isos.

infix 8 _≈_
data _≈_ : Game → Game → Set where
  bsm : ∀ {A B} → B ≲ A → A ≲ B → A ≈ B

infixl 8 _≈∘≈_

_≈∘≈_ : ∀ {A B C} → A ≈ B → B ≈ C → A ≈ C
(bsm s s') ≈∘≈ (bsm r r') = bsm (s ≲∘≲ r) (r' ≲∘≲ s')

id≈ : ∀ {G} → G ≈ G
id≈ = bsm id≲ id≲

infixr 9 _^-1

_^-1 : ∀ {M N} → M ≈ N → N ≈ M
(bsm f g) ^-1 = bsm g f

wk₁ : ∀ {M N} → M ≈ N → M ≲ N
wk₁ (bsm f g) = g

wk₂ : ∀ {M N} → M ≈ N → N ≲ M
wk₂ (bsm f g) = f

-- Composing morphisms with strategies

infixr 8 _≲∘_ _≈∘_
infixl 8 _∘≲_ _∘≈_

mutual
  _≲∘_ : ∀ {M N} → N ≲ M → Strat - N → Strat - M
  (sim h h') ≲∘ (neg f) = neg (λ i → f (h i) ∘≲ (h' i))

  _∘≲_ : ∀ {P Q} → Strat + P → Q ≲ P → Strat + Q
  (pos m g) ∘≲ (sim h h') = pos (h m) (h' m ≲∘ g)

_≈∘_ : ∀ {M N} → M ≈ N → Strat - M → Strat - N
g ≈∘ σ = (wk₁ g) ≲∘ σ

_∘≈_ : ∀ {P Q} → Strat + P → P ≈ Q → Strat + Q
σ ∘≈ f = σ ∘≲ (wk₂ f)
