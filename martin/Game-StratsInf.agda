
module Game-StratsInf where
-- in which we describe combinators on strategies, such as composition
-- and ⊗
-- but the infinite version!

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_+_ to _+'_)
open import Coinduction

open import Game-CoreInf
open import Game-MorphsInf

open import Category.Monad.Partiality as P

-- Products and coproducts

σI : Strat - I
σI = neg λ()

_σ&_ : ∀ {M N} → Strat - M → Strat - N → Strat - (M ×' N)
_σ&_ {gam m} {gam n} (neg f) (neg g) = neg  [ f , g ]

{-
σω& : ∀ {M} → (ℕ → Strat - M) → Strat - (ω× M)
σω& {gam {i} m} f = neg (λ i → aux (f (proj₁ i)) (proj₂ i))
    where aux : Strat - (gam {i} m) → (e : T i) → Strat + (m e)
          aux (neg f) e = f e
-}

pi1 : ∀ {A B} → Strat - (A ×' B) → Strat - A
pi1 {gam a} {gam b} (neg f) = neg (λ a → f (inj₁ a))

pi2 : ∀ {A B} → Strat - (A ×' B) → Strat - B
pi2 {gam a} {gam b} (neg f) = neg (λ a → f (inj₂ a))

pin : ∀ {M} → ℕ → Strat - (ω× M) → Strat - M
pin {gam a} n (neg f) = neg (λ a' → f (n , a'))

coprod : ∀ {A B} → Strat + (A ×' B) → _⊥ (Strat + A ⊎ Strat + B)
coprod {gam p} {gam g} (pos (now (inj₁ x , y))) = now (inj₁ (pos (now (x , y ))))
coprod {gam p} {gam g} (pos (now (inj₂ y , y'))) = now (inj₂ (pos (now (y , y'))))
coprod {gam p} {gam g} (pos (later x)) = later (♯ coprod (pos (♭ x)))

{-
coprodω : ∀ {A} → Strat + (ω× A) → ℕ × Strat + A
coprodω {gam p} (pos x f) = proj₁ x , pos (proj₂ x) f
-}

{-
σ⊕1 : ∀ {P} Q → Strat + P → Strat + (P ×' Q)
σ⊕1 {gam p} (gam q) (pos (now (i , f))) = pos (now (inj₁ i , f))
σ⊕1 {gam {i} p} (gam {j} q) (pos (later x))
     = pos (later (♯ (unpos $ σ⊕1 {gam {i} p} (gam {j} q) (pos (♭ x)))))
  -- the unpos needs to be expanded
-}

--σ⊕2 : ∀ {Q} P → Strat + Q → Strat + (P ×' Q)
--σ⊕2 {gam p} (gam q) (pos i f) = pos (inj₂ i) f


{-
σ⊕n : ∀ {P} → ℕ → Strat + P → Strat + (ω× P)
σ⊕n {gam p} n (pos x f) = pos (n , x) f
-}

-- Lifts

σ⊸o : ∀ {p G} → Strat p G → Strat (¬ p) (G ⊸o)
σ⊸o { - } {gam g} σ = pos (now (tt , ♯ σ))
σ⊸o { + } {gam g} σ = neg (λ x → ♯ σ)

unσ⊸o : ∀ {p G} → Strat p (G ⊸o) → _⊥ (Strat (¬ p) G)
unσ⊸o { - } {gam g} (neg f)   = now (♭ (f tt))
unσ⊸o { + } {gam g} (pos (now (_ , τ))) = now (♭ τ)
unσ⊸o { + } {gam g} (pos (later x)) = later (♯ unσ⊸o (pos (♭ x)))

-- Composition of Strategies

-- some defined in Game-CoreInf

_∙_ :  ∀ {A B C} → Strat - (B ⊸ C) → Strat - (A ⊸ B) → Strat - (A ⊸ C)
σ ∙ τ = τ ∙₁ σ

{-
_∙⁺_ : ∀ {A B C} → Strat + (C ⊘ B) → Strat - (A ⊸ B) → Strat + (C ⊘ A)
_∙⁺_ {gam a} {gam b} {gam c} (pos (j, g) σ = pos j (g ∙ σ)

_∙̂₂_ : ∀ {A B C} → Strat + (A ⊘ B) → Strat - (C ⊸ B) → Strat + (A ⊘ C)
_∙̂₂_ {gam a} {gam b} {gam c} (pos i g) σ = pos i (σ ∙₁ g)

_∙̂₁_ : ∀ {A B C} → Strat - (A ⊸̂ B) → Strat + (B ⊘ C) → Strat + (A ⊘ C)
_∙̂₁_ {gam a} {gam b} {gam c} (neg f) (pos i g) = (f i) ∙̂₂ g

_∙̂_ : ∀ {A B C} → Strat - (B ⊸̂ C) → Strat - (A ⊸̂ B) → Strat - (A ⊸̂ C)
_∙̂_ {gam a} {gam b} {gam c} (neg g) σ = neg (λ c' → σ ∙̂₁ (g c'))
-}

J : ∀ {A B} → Strat - (A ⊸̂ B) → Strat - (A ⊸ B)
J = _≲∘_ ⊸≲⊸̂

_∙`_ : ∀ {A B} → Strat - (A ⊸ B) → Strat - A → Strat - B
σ ∙` τ = unit⊸ ≈∘ (σ ∙ ((unit⊸ ^-1) ≈∘ τ))

_`∙_ : ∀ {A B} → Strat + B → Strat - (A ⊸ B) → Strat + A
τ `∙ σ = (σ ∙₂ (τ ∘≈ (dist10 ^-1))) ∘≈ dist10

lfp : ∀ {A} → Strat - (A ⊸ A) → Strat - (I ⊸ A)
lfp {gam g} (neg f) = neg (λ x → ♯ lfp (neg f) ∙₂ ♭ (f x))
 -- problem here: ∙₂ is an arbitrary function!
 -- it is very annoying if we have to "expand this out", it will mean defining
 -- a specialised form of composition here...

-- Action of ⊗, ⊘, ⊸ etc on strategies.

{-
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

copycat : ∀ {A B} → B ≲ A → Strat - (A ⊸ B)
copycat {gam a} {gam b} (sim f g) = neg (λ b' → cc' (f b') (g b'))
  where cc' : ∀ {A B} → (m : Mov A) → (A ▸ m) ≲ B → Strat + (B ⊗ A)
        cc' {gam a} {gam b} m p = pos (inj₂ m) (copycat p)

copycat_st : ∀ {A B} → B ≲ A → Strat - (A ⊸̂ B)
copycat_st {gam a} {gam b} (sim f g) = neg (λ b' → cc' (f b') (g b'))
  where cc' : ∀ {A B} → (m : Mov A) → (A ▸ m) ≲ B → Strat + (A ⊘ B)
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

sub×₂ : ∀ M N → N ≲ M ×' N
sub×₂ (gam g) (gam f) = sim inj₂ (λ _ → id≲)

π₂σ : (M N : Game) → Strat - (M ×' N ⊸ N)
π₂σ M N = copycat (sub×₂ M N)

ΛI : ∀ {M} → Strat - M → Strat - (I ⊸ M)
ΛI {M} σ = (unit⊸ ^-1) ≈∘ σ

ΛIinv : ∀ {M} → Strat - (I ⊸ M) → Strat - M
ΛIinv {M} σ = unit⊸ ≈∘ σ

Λ : ∀ {M N O} → Strat - (M ⊗ N ⊸ O) → Strat - (M ⊸ (N ⊸ O))
Λ {M} σ = (pasc⊸ ^-1) ≈∘ σ

Λinv : ∀ {M N O} → Strat - (M ⊸ (N ⊸ O)) → Strat - (M ⊗ N ⊸ O)
Λinv {M} σ = pasc⊸ ≈∘ σ

app : ∀ {N O} → Strat - ((N ⊗ (N ⊸ O)) ⊸ O)
app {N} {O} = (sym⊗ ≈⊸ _) ≈∘ (Λinv idσ)

-}