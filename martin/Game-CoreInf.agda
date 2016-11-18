
module Game-CoreInf where
-- in which we formalise the fundamentals of Game Semantics in Agda
-- but an infinitary version!

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Coinduction
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
-- a corresponding (delayed) "rest of the game":

data Game : Set where
  gam : {ι : MovEnc} → (T ι → ∞ Game) → Game

mvEnc : Game → MovEnc
mvEnc (gam {a} f) = a

Mov : Game → Set
Mov G = T (mvEnc G)

infix 10 _▸_
_▸_ : (G : Game) → Mov G → Game
(gam {ι} f) ▸ x = ♭ (f x)

-- Constructions on Games

I : Game
I = gam {nil} ⊥-elim

_×'_ : Game → Game → Game
gam {i} f ×' gam {j} g = gam {i ⊹ j} ([ f , g ])

infix 14 _⊗_
infix 12 _⊸_ _⊸̂_

mutual
  _⊸_ : Game → Game → Game
  G ⊸ (gam {i} f) = gam {i} (λ i' → ♯ (♭ (f i') ⊗ G))

  _⊗_ : Game → Game → Game
  (gam {i} f) ⊗ (gam {j} g) = gam {i ⊹ j} h
   where h : T (i ⊹ j) → ∞ Game
         h (inj₁ x) = ♯ (gam {j} g ⊸ ♭ (f x))
         h (inj₂ y) = ♯ (gam {i} f ⊸ ♭ (g y))

_⊘_ : Game → Game → Game
(gam {i} f) ⊘ G = gam {i} (λ i' → ♯ (G ⊸ (♭ $ f i')))

o : Game
o = gam {one} (λ _ → ♯ I)

bangΣ : Game
bangΣ = gam {one} (λ _ → ♯ bangΣ)

_⊸o : Game → Game
G ⊸o = gam {one} (λ tt → ♯ G)

ω× : Game → Game
ω× (gam {i} f) = gam {ℕ× i} (λ x → ♯ (♭ $ f (proj₂ x)))

-- ⊸̂ represents a strict function space:

_⊸̂_ : Game → Game → Game
G ⊸̂ (gam {i} f) = gam {i} (λ i' → ♯ (G ⊘ ♭ (f i')))

-- Exponential
-- bang G = G ⊘ bang G

data GameP : Set where
  gam : {ι : MovEnc} → (T ι → ∞ GameP) → GameP
  _⊸P_ : GameP → GameP → GameP
  _⊗P_ : GameP → GameP → GameP

data GameH : Set where
  gam : {ι : MovEnc} → (T ι → ∞ GameP) → GameH

HtoP : GameH → GameP
HtoP (gam {i} y) = gam {i} y

GtoP : Game → GameP
GtoP (gam {i} y) = gam {i} (λ x → ♯ (GtoP (♭ (y x))))

whnf : GameP → GameH
whnf (gam {i} y) = gam {i} y
whnf (y ⊸P y') = (whnf y) ⊸' (whnf y')
   where _⊸'_ : GameH → GameH → GameH
         G ⊸' gam {i} y = gam {i} (λ x → ♯ (♭ (y x) ⊗P (HtoP G)))
whnf (y ⊗P y') = (whnf y) ⊗' (whnf y')
   where _⊗'_ : GameH → GameH → GameH
         gam {i} z ⊗' gam {j} y = gam {i ⊹ j} [ (λ zi → ♯ ((gam {j} y) ⊸P (♭ (z zi)))) ,
                                                 (λ zi → ♯ ((gam {i} z) ⊸P (♭ (y zi)))) ]

mutual
  HtoG : GameH → Game
  HtoG (gam {i} y) = gam {i} (λ x → ♯ (PtoG (♭ (y x))))

  PtoG : GameP → Game
  PtoG g = HtoG (whnf g)
  
bangP : Game → GameP
bangP (gam {i} f) = gam {i} (λ x → ♯ (bangP (gam {i} f) ⊸P GtoP (♭ (f x))))

bang : Game → Game
bang g = PtoG $ bangP g

-- Strategies

{-
open import Data.Bool public
   renaming (true to -  ; false to +;
             Bool to Pol; not   to ¬;
             T to IsTrue)

open import Category.Monad.Partiality as P
open import Category.Functor
open import Category.Monad
open RawMonad P.monad using (_<$>_)

data Strat : Pol → Game → Set where
  pos : ∀ {G} → _⊥ (Σ (Mov G) (λ i → ∞ (Strat - (G ▸ i)))) → Strat + G
  neg : ∀ {G} → ((i : Mov G) → ∞ (Strat + (G ▸ i))) → Strat - G

swp' : ∀ {B} {C} → (Σ (T (mvEnc (C ⊗ B))) (λ i → ∞ (Strat - (C ⊗ B ▸ i))) →
         Σ (T (mvEnc (B ⊗ C))) (λ i → ∞ (Strat - (B ⊗ C ▸ i))))
swp' {gam f} {gam g} (inj₁ x , y') = inj₂ x , y'
swp' {gam f} {gam g} (inj₂ y' , y0) = inj₁ y' , y0

swp : ∀ {B C} → Strat + (C ⊗ B) → Strat + (B ⊗ C)
swp {B} {C} (pos y) = pos (swp' {B} {C} <$> y)

unpos : ∀ {G} → Strat + G → _⊥ (Σ (Mov G) (λ i → ∞ (Strat - (G ▸ i))))
unpos (pos y) = y

{-mutual
  _∙₁_ : ∀ {A B C} → Strat - (A ⊸ B) → Strat - (B ⊸ C) → Strat - (A ⊸ C)
  _∙₁_ {gam a} {gam b} {gam c} σ (neg g) = neg (λ c' → σ ∙₂ (g c'))

  _∙₂_ : ∀ {A B C} → Strat - (A ⊸ B) → Strat + (C ⊗ B) → Strat + (C ⊗ A)
  _∙₂_ {gam a} {gam b} {gam c} σ       (pos (inj₁ c') g) = pos (inj₁ c') (σ ∙₁ g)
  _∙₂_ {gam a} {gam b} {gam c} (neg f) (pos (inj₂ b') g) = swp $ g ∙₂ (swp $ f b')
-}

mutual
  _∙₁_ : ∀ {A B C} → Strat - (A ⊸ B) → Strat - (B ⊸ C) → Strat - (A ⊸ C)
  _∙₁_ {gam a} {gam b} {gam c} σ (neg g) = neg (λ c' → ♯ σ ∙₂ (♭ (g c')))

  _∙₂'_ : ∀ {A B C} → Strat - (A ⊸ B) →
             _⊥ (Σ (T (mvEnc (C ⊗ B))) (λ i → ∞ (Strat - (C ⊗ B ▸ i)))) →
              _⊥ (Σ (T (mvEnc (C ⊗ A))) (λ i → ∞ (Strat - (C ⊗ A ▸ i))))
  _∙₂'_ {gam a} {gam b} {gam c} σ (now (inj₁ x , y))
         = now (inj₁ x , ♯ σ ∙₁ ♭ y)
  _∙₂'_ {gam a} {gam b} {gam c} (neg y) (now (inj₂ y' , y0))
         = later (♯ (♭ y0) ∙₃' (unpos $ ♭ (y y')))
  _∙₂'_ {gam a} {gam b} {gam {i} c} σ (later x)
         = later (♯ _∙₂'_ {gam a} {gam b} {gam {i} c} σ (♭ x)) 

  _∙₃'_ : ∀ {A B C} → Strat - (A ⊸ B) →
             _⊥ (Σ (T (mvEnc (B ⊗ C))) (λ i → ∞ (Strat - (B ⊗ C ▸ i)))) →
              _⊥ (Σ (T (mvEnc (A ⊗ C))) (λ i → ∞ (Strat - (A ⊗ C ▸ i))))
  _∙₃'_ {gam a} {gam b} {gam c} σ (now (inj₂ x , y))
         = now (inj₂ x , ♯ σ ∙₁ ♭ y)
  _∙₃'_ {gam a} {gam b} {gam c} (neg y) (now (inj₁ y' , y0))
         = later (♯ ((♭ y0) ∙₂' (swp' {gam a} {♭ (b y')} <$> (unpos $ ♭ (y y')))))
  _∙₃'_ {gam a} {gam b} {gam {i} c} σ (later x)
         = later (♯ _∙₃'_ {gam a} {gam b} {gam {i} c} σ (♭ x)) 

  _∙₂_ : ∀ {A B C} → Strat - (A ⊸ B) → Strat + (C ⊗ B) → Strat + (C ⊗ A)
  _∙₂_ {A} {B} {C} σ (pos y) = pos (σ ∙₂' y)

-- If we consider a positive game Q, a P-strategy on Q is given by a
-- term of type Strat + Q.

-}

-- Game morphisms

-- An element of A ≲ B represents a copycat-shaped strategy on A ⊸ B,
-- but it is more convinient to work with and we need to define a lot
-- of these things.


infix 8 _≲_
data _≲_ : Game → Game → Set where
  sim : ∀ {A B} →
        (h : Mov A → Mov B) →
        ((i' : Mov A) → ∞ (B ▸ (h i') ≲ (A ▸ i'))) →
        A ≲ B

id≲ : ∀ {G} → G ≲ G
id≲ {gam f} = sim id (λ i → ♯ id≲ {♭ (f i)})


infixl 8 _≲∘≲_

_≲∘≲_ : ∀ {A B C} → A ≲ B → B ≲ C → A ≲ C
(sim f f') ≲∘≲ (sim g g') = sim (g ∘ f) (λ x → ♯ (♭ (g' (f x)) ≲∘≲ ♭ ((f' x))))


-- We bundle two-way copycat strategies into a ≈ structure.
-- This is how we represent isos.

infix 8 _≈_
data _≈_ : Game → Game → Set where
  bsm : ∀ {A B} → A ≲ B → B ≲ A → A ≈ B

infixl 8 _≈∘≈_

_≈∘≈_ : ∀ {A B C} → A ≈ B → B ≈ C → A ≈ C
(bsm s s') ≈∘≈ (bsm r r') = bsm (s ≲∘≲ r) (r' ≲∘≲ s')

id≈ : ∀ {G} → G ≈ G
id≈ = bsm id≲ id≲

infixr 9 _^-1

_^-1 : ∀ {M N} → M ≈ N → N ≈ M
(bsm f g) ^-1 = bsm g f

wk₁ : ∀ {M N} → M ≈ N → M ≲ N
wk₁ (bsm f g) = f

wk₂ : ∀ {M N} → M ≈ N → N ≲ M
wk₂ (bsm f g) = g


-- Composing morphisms with strategies

{-
infixr 8 _≲∘_ -- _≈∘_
infixl 8 _∘≲_ -- _∘≈_

mutual
  _≲∘_ : ∀ {M N} → M ≲ N → Strat - N → Strat - M
  (sim h h') ≲∘ (neg f) = neg (λ i → ♯ (♭ (f (h i)) ∘≲ ♭ (h' i)))

  _∘≲_ : ∀ {P Q} → Strat + P → P ≲ Q → Strat + Q
  _∘≲_ {P} {Q} (pos y) (sim h y') = pos (_∘≲'_ {P} {Q} y h y')

  _∘≲'_ : ∀ {P Q} → _⊥ (Σ (T (mvEnc P)) (λ i → ∞ (Strat - (P ▸ i)))) → 
               (h : T (mvEnc P) → T (mvEnc Q)) → ((i' : T (mvEnc P)) → ∞ (Q ▸ h i' ≲ P ▸ i'))
                   → _⊥ (Σ (Mov Q) (λ i → ∞ (Strat - (Q ▸ i))))
  _∘≲'_ {P} {Q} (now (x , y)) h y' = now (h x , (♯ (♭ (y' x) ≲∘ (♭ y))))
  _∘≲'_ {P} {Q} (later x) h y' = later (♯ (_∘≲'_ {P} {Q} (♭ x) h y'))

_≈∘_ : ∀ {M N} → M ≈ N → Strat - M → Strat - N
g ≈∘ σ = (wk₂ g) ≲∘ σ

_∘≈_ : ∀ {P Q} → Strat + P → P ≈ Q → Strat + Q
σ ∘≈ f = σ ∘≲ (wk₁ f)

-}