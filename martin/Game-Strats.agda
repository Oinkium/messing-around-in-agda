module Game-Strats where
-- in which we describe combinators on strategies, such as composition
-- and ⊗

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_+_ to _+'_)

open import Game-Core
open import Game-Morphs

-- Products and coproducts

σI : Strat - I
σI = neg λ()

_σ&_ : ∀ {M N} → Strat - M → Strat - N → Strat - (M ×' N)
_σ&_ {gam m} {gam n} (neg f) (neg g) = neg  [ f , g ]

σω& : ∀ {M} → (ℕ → Strat - M) → Strat - (ω× M)
σω& {gam {i} m} f = neg (λ i → aux (f (proj₁ i)) (proj₂ i))
    where aux : Strat - (gam {i} m) → (e : T i) → Strat + (m e)
          aux (neg f) e = f e

pi1 : ∀ {A B} → Strat - (A ×' B) → Strat - A
pi1 {gam a} {gam b} (neg f) = neg (λ a → f (inj₁ a))

pi2 : ∀ {A B} → Strat - (A ×' B) → Strat - B
pi2 {gam a} {gam b} (neg f) = neg (λ a → f (inj₂ a))

pin : ∀ {M} → ℕ → Strat - (ω× M) → Strat - M
pin {gam a} n (neg f) = neg (λ a' → f (n , a'))

coprod : ∀ {A B} → Strat + (A ×' B) → Strat + A ⊎ Strat + B
coprod {gam p} {gam q} (pos (inj₁ a) f) = inj₁ (pos a f)
coprod {gam p} {gam q} (pos (inj₂ b) f) = inj₂ (pos b f)

coprodω : ∀ {A} → Strat + (ω× A) → ℕ × Strat + A
coprodω {gam p} (pos x f) = proj₁ x , pos (proj₂ x) f

σ⊕1 : ∀ {P} Q → Strat + P → Strat + (P ×' Q)
σ⊕1 {gam p} (gam q) (pos i f) = pos (inj₁ i) f

σ⊕2 : ∀ {Q} P → Strat + Q → Strat + (P ×' Q)
σ⊕2 {gam p} (gam q) (pos i f) = pos (inj₂ i) f

σ⊕n : ∀ {P} → ℕ → Strat + P → Strat + (ω× P)
σ⊕n {gam p} n (pos x f) = pos (n , x) f
 
-- Lifts

σ⊸o : ∀ {p G} → Strat p G → Strat (¬ p) (G ⊸o)
σ⊸o { - } {gam g} σ = pos tt     σ
σ⊸o { + } {gam g} σ = neg (λ x → σ)

unσ⊸o : ∀ {p G} → Strat p (G ⊸o) → Strat (¬ p) G
unσ⊸o { - } {gam g} (neg f)    = f tt
unσ⊸o { + } {gam g} (pos _ τ) = τ

-- Composition of Strategies

swp : ∀ {B C} → Strat + (C ⊗ B) → Strat + (B ⊗ C)
swp {gam b} {gam c} (pos (inj₁ x) f) = pos (inj₂ x) f
swp {gam b} {gam c} (pos (inj₂ y) f) = pos (inj₁ y) f

mutual
  _∙₁_ : ∀ {A B C} → Strat - (A ⊸ B) → Strat - (B ⊸ C) → Strat - (A ⊸ C)
  _∙₁_ {gam a} {gam b} {gam c} σ (neg g) = neg (λ c' → σ ∙₂ (g c'))

  _∙₂_ : ∀ {A B C} → Strat - (A ⊸ B) → Strat + (C ⊗ B) → Strat + (C ⊗ A)
  _∙₂_ {gam a} {gam b} {gam c} σ       (pos (inj₁ c') g) = pos (inj₁ c') (σ ∙₁ g)
  _∙₂_ {gam a} {gam b} {gam c} (neg f) (pos (inj₂ b') g) = swp $ g ∙₂ (swp $ f b')

_∙_ :  ∀ {A B C} → Strat - (B ⊸ C) → Strat - (A ⊸ B) → Strat - (A ⊸ C)
σ ∙ τ = τ ∙₁ σ

_∙⁺_ : ∀ {A B C} → Strat + (C ⊘ B) → Strat - (A ⊸ B) → Strat + (C ⊘ A)
_∙⁺_ {gam a} {gam b} {gam c} (pos j g) σ = pos j (g ∙ σ)

_∙̂₂_ : ∀ {A B C} → Strat + (A ⊘ B) → Strat - (C ⊸ B) → Strat + (A ⊘ C)
_∙̂₂_ {gam a} {gam b} {gam c} (pos i g) σ = pos i (σ ∙₁ g)

_∙̂₁_ : ∀ {A B C} → Strat - (A ⊸̂ B) → Strat + (B ⊘ C) → Strat + (A ⊘ C)
_∙̂₁_ {gam a} {gam b} {gam c} (neg f) (pos i g) = (f i) ∙̂₂ g

_∙̂_ : ∀ {A B C} → Strat - (B ⊸̂ C) → Strat - (A ⊸̂ B) → Strat - (A ⊸̂ C)
_∙̂_ {gam a} {gam b} {gam c} (neg g) σ = neg (λ c' → σ ∙̂₁ (g c'))

J : ∀ {A B} → Strat - (A ⊸̂ B) → Strat - (A ⊸ B)
J = _≲∘_ ⊸≲⊸̂

_∙`_ : ∀ {A B} → Strat - (A ⊸ B) → Strat - A → Strat - B
σ ∙` τ = unit⊸ ≈∘ (σ ∙ (unit⊸ ^-1 ≈∘ τ))

_`∙_ : ∀ {A B} → Strat + B → Strat - (A ⊸ B) → Strat + A
τ `∙ σ = (σ ∙₂ (τ ∘≈ dist10 ^-1)) ∘≈ dist10

-- Action of ⊗, ⊘, ⊸ etc on strategies.

mutual
  _⊗s_ : ∀ {A B C D} → Strat - (A ⊸ B) → Strat - (C ⊸ D)
         → Strat - ((A ⊗ C) ⊸ (B ⊗ D))
  _⊗s_ {gam a} {gam b} {gam c} {gam d} (neg f) (neg g)
     = neg [ (λ x → f x ⊗s₁ (neg g)) ,
             (λ x → (g x ⊗s₁ (neg f)) ∘≈ ( _ ⊗≈ sym⊗)) ]

  _⊗s₁_ : ∀ {A B C D} → Strat + (B ⊗ A) → Strat - (C ⊸ D)
          → Strat + ((D ⊸ B) ⊗ (A ⊗ C))
  _⊗s₁_ {gam a} {gam b} {gam c} {gam d} (pos (inj₁ x) f) σ
      = pos (inj₁ x) (f ⊗s σ)
  _⊗s₁_ {gam a} {gam b} {gam c} {gam d} (pos (inj₂ y) f) σ
      = pos (inj₂ $ inj₁ y) (σ ⊸s f)

  _⊸s_ : ∀ {A B C D} → Strat - (C ⊸ A) → Strat - (B ⊸ D)
         → Strat - ((A ⊸ B) ⊸ (C ⊸ D))
  _⊸s_ {gam a} {gam b} {gam c} {gam d} σ (neg g)
     = neg (λ x → σ ⊸s₁ (g x))

  _⊸s₁_ : ∀ {A B C D} → Strat - (C ⊸ A) → Strat + (D ⊗ B)
          → Strat + ((D ⊗ C) ⊗ (A ⊸ B))
  _⊸s₁_ σ τ = ((τ ∘≈ sym⊗) ⊗s₁ σ) ∘≈ sym⊗

_⊘s₁_ : ∀ {A B C D} → Strat + (A ⊘ B) → Strat - (C ⊸ D)
   → Strat + ((A ⊘ C) ⊘ (D ⊸ B))
_⊘s₁_ {gam a} {gam b} {gam c} {gam d} (pos i f) σ
   = pos i (σ ⊸s f)

_⊘s_ : ∀ {A B C D} → Strat - (A ⊸̂ B) → Strat - (C ⊸ D)
   → Strat - (A ⊘ C ⊸̂ B ⊘ D) 
_⊘s_ {gam a} {gam b} {gam c} {gam d} (neg f) σ
   = neg (λ b' → f b' ⊘s₁ σ)

_⊸ŝ₁_ : ∀ {A B C D} → Strat - (C ⊸ A) → Strat + (B ⊘ D)
    → Strat + ((A ⊸ B) ⊘ (D ⊗ C))
_⊸ŝ₁_ {gam a} {gam b} {gam c} {gam d} σ (pos i g)
   = pos i (g ⊗s σ)

_⊸ŝ_ : ∀ {A B C D} → Strat - (C ⊸ A) → Strat - (B ⊸̂ D)
       → Strat - ((A ⊸ B) ⊸̂ (C ⊸ D))
_⊸ŝ_ {gam a} {gam b} {gam c} {gam d} σ (neg g)
   = neg (λ x → σ ⊸ŝ₁ (g x))

-- Copycat Strategies from ≲

copycat : ∀ {A B} → A ≲ B → Strat - (A ⊸ B)
copycat {gam a} {gam b} (sim f g) = neg (λ b' → cc' (f b') (g b'))
  where cc' : ∀ {A B} → (m : Mov A) → B ≲ (A ▸ m)→ Strat + (B ⊗ A)
        cc' {gam a} {gam b} m p = pos (inj₂ m) (copycat p)

copycat_st : ∀ {A B} → A ≲ B → Strat - (A ⊸̂ B)
copycat_st {gam a} {gam b} (sim f g) = neg (λ b' → cc' (f b') (g b'))
  where cc' : ∀ {A B} → (m : Mov A) → B ≲ (A ▸ m) → Strat + (A ⊘ B)
        cc' {gam a} {gam b} m p = pos m (copycat p)

idσ : ∀ {A} → Strat - (A ⊸ A)
idσ = copycat id≲

idσs : ∀ {A} → Strat - (A ⊸̂ A)
idσs = copycat_st id≲

symσ : ∀ M N → Strat - ((M ⊗ N) ⊸ (N ⊗ M))
symσ M N = copycat (wk₁ sym⊗)

π₁⊗σ : ∀ M N → Strat - (M ⊗ N ⊸ M)
π₁⊗σ M N = copycat ≲⊗af

π₂⊗σ : ∀ M N → Strat - (M ⊗ N ⊸ N)
π₂⊗σ M N = (π₁⊗σ N M) ∙ (symσ M N)

π₁σ : ∀ M N → Strat - (M ×' N ⊸ M)
π₁σ M N = copycat ≲π₁

sub×₂ : ∀ M N → M ×' N ≲ N
sub×₂ (gam g) (gam f) = sim inj₂ (λ _ → id≲)

π₂σ : (M N : Game) → Strat - (M ×' N ⊸ N)
π₂σ M N = copycat (sub×₂ M N)

ΛI : ∀ {M} → Strat - M → Strat - (I ⊸ M)
ΛI {M} σ = unit⊸ ^-1 ≈∘ σ

ΛIinv : ∀ {M} → Strat - (I ⊸ M) → Strat - M
ΛIinv {M} σ = unit⊸ ≈∘ σ

Λ : ∀ {M N O} → Strat - (M ⊗ N ⊸ O) → Strat - (M ⊸ (N ⊸ O))
Λ {M} σ = pasc⊸ ^-1 ≈∘ σ

Λinv : ∀ {M N O} → Strat - (M ⊸ (N ⊸ O)) → Strat - (M ⊗ N ⊸ O)
Λinv {M} σ = pasc⊸ ≈∘ σ

app : ∀ {N O} → Strat - ((N ⊗ (N ⊸ O)) ⊸ O)
app {N} {O} = sym⊗ ≈⊸ _ ≈∘ Λinv idσ

top : Strat + o
top = pos tt σI

noσo : Strat - o → ⊥
noσo (neg y) = f (y tt)
     where f : Strat + I → ⊥
           f (pos () y') 

