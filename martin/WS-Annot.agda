module WS-Annot where
-- in which we describe annotated games, and construct them out of WS
-- formulas

open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_,_ to _,'_)
open import Relation.Binary.PropositionalEquality
open import Data.String
open import Function

open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_ )
open import WS-Syn
open import WS-Sem-Fsc

-- Our goal is to construct a function:
--   anotate : ∀ {p} (A : Fml p) → Annotation ⟦ A ⟧ (λ _ → PolFml)
-- annotating each game with some formula with a PolFml, i.e. a
-- formula of some polarity.

-- To do this, we first need a notion of semantic-annotated syntax:

data FML : Pol → Game → Set where
  F0   : FML + I
  F1   : FML - I
  F⊤   : FML + o
  F⊥   : FML - o
  _⊗_  : ∀ {G H} (M : FML - G)(N : FML - H) → FML - (G ⊗' H)
  _⅋_  : ∀ {G H} (P : FML + G)(Q : FML + H) → FML + (G ⊗' H)
  _&_  : ∀ {G H} (M : FML - G)(N : FML - H) → FML - (G ×' H)
  _⊕_  : ∀ {G H} (P : FML + G)(Q : FML + H) → FML + (G ×' H)
  ω&  : ∀ {G} (M : FML - G) → FML - (ω× G)
  ω⊕  : ∀ {G} (P : FML + G) → FML + (ω× G)

  _-⊘_ : ∀ {G H} (M : FML - G)(N : FML - H) → FML - (G ⊘' H)
  _+◁_ : ∀ {G H} (P : FML + G)(Q : FML + H) → FML + (G ⊘' H)

  _+⊘_ : ∀ {G H} (P : FML + G)(N : FML - H) → FML + (H ⊸  G)
  _-◁_ : ∀ {G H} (M : FML - G)(P : FML + H) → FML - (H ⊸  G)

toFml : ∀ {pol}{G}(A : FML pol G) → Fml pol
toFml F0       = F0
toFml F1       = F1
toFml F⊤       = F⊤
toFml F⊥       = F⊥
toFml (M ⊗ N)  = (toFml M) ⊗ (toFml N)
toFml (P ⅋ Q)  = (toFml P) ⅋ (toFml Q)
toFml (M & N)  = (toFml M) & (toFml N)
toFml (P ⊕ Q)  = (toFml P) ⊕ (toFml Q)
toFml (M -⊘ N) = (toFml M) ⊘ (toFml N)
toFml (P +◁ Q) = (toFml P) ◁ (toFml Q)
toFml (P +⊘ N) = (toFml P) ⊘ (toFml N)
toFml (M -◁ P) = (toFml M) ◁ (toFml P)
toFml (ω& M)   = ω& (toFml M)
toFml (ω⊕ P)   = ω⊕ (toFml P)

toFML : ∀ {pol}(A : Fml pol) → FML pol ⟦ A ⟧
toFML F0              = F0 
toFML F1              = F1
toFML F⊥              = F⊥
toFML F⊤              = F⊤
toFML (M ⊗ N)         = (toFML M) ⊗ (toFML N)
toFML (P ⅋ Q)         = (toFML P) ⅋ (toFML Q)
toFML (P ⊕ Q)         = (toFML P) ⊕ (toFML Q)
toFML (M & N)         = (toFML M) & (toFML N)
toFML (ω& N)          = ω& (toFML N)
toFML (ω⊕ P)          = ω⊕ (toFML P)
toFML (_⊘_ { + } A M) = (toFML  A) +⊘ (toFML M)
toFML (_⊘_ { - } A M) = (toFML  A) -⊘ (toFML M)
toFML (_◁_ { + } A M) = (toFML  A) +◁ (toFML M)
toFML (_◁_ { - } A M) = (toFML  A) -◁ (toFML M)

-- Annotation functions

mutual
  annot+ : ∀ {G} (P : FML + G)(i : Mov G) → FML - (G ▸ i)
  annot+ F0                         ()
  annot+ F⊤                         tt         = F1
  annot+ (_⅋_  {gam _} {gam _} P Q) (inj₁ i) = annot+ P i -◁ Q
  annot+ (_⅋_  {gam _} {gam _} P Q) (inj₂ j) = annot+ Q j -◁ P
  annot+ (_⊕_  {gam _} {gam _} P Q) (inj₁ i) = annot+ P i
  annot+ (_⊕_  {gam _} {gam _} P Q) (inj₂ j) = annot+ Q j
  annot+ (ω⊕   {gam _} P) m                  = annot+ P (proj₂ m)
  annot+ (_+◁_ {gam _} {gam _} P Q) i        = annot+ P i -◁ Q
  annot+ (_+⊘_ {gam _} {gam _} P N) i        = annot+ P i ⊗ N

  annot- : ∀ {G} (M : FML - G)(i : Mov G) → FML + (G ▸ i)
  annot- F1                         ()
  annot- F⊥                         tt       = F0
  annot- (_⊗_  {gam _} {gam _} M N) (inj₁ i) = annot- M i +⊘ N
  annot- (_⊗_  {gam _} {gam _} M N) (inj₂ j) = annot- N j +⊘ M
  annot- (_&_  {gam _} {gam _} M N) (inj₁ i) = annot- M i
  annot- (ω& {gam _} M) m                    = annot- M (proj₂ m)
  annot- (_&_  {gam _} {gam _} M N) (inj₂ j) = annot- N j
  annot- (_-⊘_ {gam _} {gam _} M N) i        = annot- M i +⊘ N
  annot- (_-◁_ {gam _} {gam _} M P) i        = annot- M i ⅋ P


annot : ∀ {pol G}(A : FML pol G)(i : Mov G) → FML (¬ pol) (G ▸ i)
annot { + } = annot+
annot { - } = annot-

PolFML : Game → Set
PolFML G = Σ Pol (λ p → FML p G)

-- anotate' takes a formula whose semantics is G, and anotates G by
-- (semantic-anotated) formulas. The type had to be this strong for
-- the induction to work.

anotate' : ∀ {p} {G} (A : FML p G) → Annotation G PolFML
anotate' {p} {gam f} A = ν (p ,' A) (λ i → anotate' {¬ p} $ annot {p} A i)

-- We can now construct the function anotate by an appropriate
-- weakening:

forget : ∀ {G} → Annotation G PolFML → Annotation G (λ _ → PolFml)
forget {gam g} (ν (p ,' A) f) = ν (p ,' toFml A) (λ i → forget (f i))

anotate : ∀ {p} (A : Fml p) → Annotation ⟦ A ⟧ (λ _ → PolFml)
anotate = forget ∘ anotate' ∘ toFML

