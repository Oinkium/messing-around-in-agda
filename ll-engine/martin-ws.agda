module linear-logic where

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_+_ to _+'_)

data MoveEnc : Set where
  nil : MoveEnc
  one : MoveEnc
  _++_ : MoveEnc -> (MoveEnc -> MoveEnc)

T : MoveEnc -> Set
T nil = ⊥
T one = ⊤
T (x ++ y) = T x ⊎ T y

data Forest : Set where
  gam : {ι : MoveEnc} -> ((T ι -> Forest) -> Forest)

Game : Set
Game = Forest

Mov : Game -> Set
Mov (gam {a} f) = T a
_≫_ : (G : Game) -> (Mov G -> Game)
gam {ι} f ≫ i = f i

I : Game
I = gam {nil} ⊥-elim

o : Game
o = gam {one} (λ _ -> I)

_×'_ : Game -> (Game -> Game)
gam {i} f ×' gam {j} g = (gam {i ++ j}) ([_,_] f g)

mutual

  _⊸_ : Game -> (Game -> Game)
  G ⊸ gam {i} f = gam {i} (λ e -> f e ⊗ G)

  _⊘_ : Game -> (Game -> Game)
  gam {i} f ⊘ G = gam {i} (λ e -> G ⊸ f e)

  _⊗_ : Game -> (Game -> Game)
  G ⊗ H = (G ⊘ H) ×' (H ⊘ G)

open import Data.Bool public
  renaming (true to - ; false to + ;
            Bool to Pol ; not to ¬ ;
            T to IsTrue)

data Strat : Pol -> (Game -> Set) where
  pos : ∀ {G} -> ((i : Mov G) -> ( Strat - (G ≫ i) -> Strat + G))
  neg : ∀ {G} -> ((i : Mov G) -> ( Strat + (G ≫ i) -> Strat - G))



