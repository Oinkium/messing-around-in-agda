open import Categories.Category

module CommutativeDiagrams {o ℓ ee} (𝒞 : Category o ℓ ee) where

open import Categories.Support.PropositionalEquality

open import Level
  using (_⊔_; suc)

open Category 𝒞
open Category.Equiv 𝒞

-- arrow : (A B : Obj) → A ⇒ B → A ⇒ B
-- arrow A B f = f
-- 
-- syntax arrow A B f = A - f ⟶ B

infix 1 _⟶_-_
infix 5 _↓
infix 5 ↓_

_⟶_-_ : {A B C : Obj} → A ⇒ B → Obj → B ⇒ C → A ⇒ C
f ⟶ B - g = g ∘ f

_↓ : {A B : Obj} → A ⇒ B → A ⇒ B
f ↓ = f

↓_ : {A B : Obj} → A ⇒ B → A ⇒ B
↓ f = f

record Square {nw ne sw se : Obj} : Set (o ⊔ ℓ) where
  constructor newSq
  field
    n : nw ⇒ ne
    w : nw ⇒ sw
    e : ne ⇒ se
    s : sw ⇒ se

infix 20 _-_⟶_↓_↓_#_-_⟶_

syntax newSq {nw} {ne} {sw} {se} n w e s = nw - n ⟶ ne ↓ w ↓ e # sw - s ⟶ se

test : (A : Obj) → Square
test A =
  A - id ⟶ A
  ↓ id     ↓ id    #
  A - id ⟶ A

infix 1 _commutes

_commutes : {nw ne sw se : Obj} → Square {nw} {ne} {sw} {se} → Set _
sq commutes = CommutativeSquare (Square.n sq) (Square.w sq) (Square.e sq) (Square.s sq)

.test-commutes : (A : Obj) → (test A) commutes
test-commutes A = refl

test2 : (A : Obj) → Square
test2 A =
  A - id ⟶ A - id ⟶ A
  ↓ id              ↓ id    #
  A   -    id    ⟶  A

.test2-commutes : (A : Obj) → (test2 A) commutes
test2-commutes A = ∘-resp-≡ʳ identityˡ

.test3 : (A : Obj) →
  A - id ⟶ A - id ⟶ A
  ↓ id              ↓ id    #
  A - id ⟶ A - id ⟶ A commutes
test3 A = sym assoc

record CommSquare {nw ne sw se : Obj} : Set (ee ⊔ suc (o ⊔ ℓ)) where
  field
    square : Square {nw} {ne} {sw} {se}
    .commutes : square commutes

paste : {A B C D E F : Obj} → (□ : CommSquare {A} {B} {D} {E}) → (■ : CommSquare {B} {C} {E} {F}) → .(Square.e (CommSquare.square □) ≡ Square.w (CommSquare.square ■)) → CommSquare {A} {C} {D} {F}
paste □ ■ p = record {
  square = record {
    n = (Square.n ◾) ∘ (Square.n ◽) ;
    w = Square.w ◽ ;
    e = Square.e ◾ ;
    s = (Square.s ◾) ∘ (Square.s ◽)
    } ;
  commutes = begin
               (h ∘ g) ∘ x
             ↓⟨ assoc ⟩
               h ∘ (g ∘ x)
             ↓⟨ ∘-resp-≡ʳ pf₂ ⟩
               h ∘ (y ∘ i)
             ↑⟨ assoc ⟩
               (h ∘ y) ∘ i
             ↓⟨ ∘-resp-≡ˡ pf₁ ⟩
               (z ∘ f) ∘ i
             ↓⟨ assoc ⟩
               z ∘ (f ∘ i)
             ∎
  }
  where
  open HomReasoning
  ◾ = CommSquare.square ■
  ◽ = CommSquare.square □
  h = Square.
