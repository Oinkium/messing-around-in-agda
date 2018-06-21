module NotGp where

open import WrongGp

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary
open import Algebra.Structures

open import Algebra.FunctionProperties

open import Data.Product

open import Level

open import Data.Integer
open import Data.Integer.Properties

open import Data.Bool

open import Bracketing
open import Data.List

data notGp : Set where
  e : notGp
  x : notGp
  _✶_ : notGp → notGp → notGp
  _⁻¹ : notGp → notGp

infix 0 _≈_

data _≈_ : Rel notGp Level.zero where
  refl    : Reflexive _≈_
  sym     : Symmetric _≈_
  trans   : Transitive _≈_
  assoc   : Associative _≈_ _✶_
  rightId : RightIdentity _≈_ e _✶_
  leftInv : LeftInverse _≈_ e _⁻¹ _✶_
  ✶-cong  : _✶_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ⁻¹-cong : _⁻¹ Preserves _≈_ ⟶ _≈_

isSemiGp : IsSemigroup _≈_ _✶_
isSemiGp = record {
  isEquivalence = record {
    refl  = refl;
    sym   = sym;
    trans = trans};
  assoc  = assoc;
  ∙-cong = ✶-cong}
  

isWrongGp : IsWrongGp _≈_ _✶_ e _⁻¹
isWrongGp = record {
  isSemigroup   = isSemiGp;
  rightIdentity = rightId;
  leftInverse   = leftInv;
  ⁻¹-cong       = ⁻¹-cong}

NotGp : WrongGp Level.zero Level.zero
NotGp = record {
  Carrier   = notGp;
  _≈_       = _≈_;
  _✶_       = _✶_;
  e         = e;
  _⁻¹       = _⁻¹;
  isWrongGp = isWrongGp}

balance : notGp → ℤ
balance e = + 0
balance x = + 1
balance (s ✶ t) = (balance s) + (balance t)
balance (s ⁻¹) = - (balance s)

balance-is-≈-invariant : balance Preserves _≈_ ⟶ _≡_
balance-is-≈-invariant refl = ≡-refl
balance-is-≈-invariant (sym t≈s) = ≡-sym (balance-is-≈-invariant t≈s)
balance-is-≈-invariant (trans s≈u u≈t) = ≡-trans (balance-is-≈-invariant s≈u) (balance-is-≈-invariant u≈t)
balance-is-≈-invariant (assoc s t u) = +-assoc (balance s) (balance t) (balance u)
balance-is-≈-invariant (rightId s) = +-identityʳ (balance s)
balance-is-≈-invariant (leftInv s) = inverseˡ (balance s)
balance-is-≈-invariant (✶-cong s≈t s′≈t′) = cong₂ _+_ (balance-is-≈-invariant s≈t) (balance-is-≈-invariant s′≈t′)
balance-is-≈-invariant (⁻¹-cong s≈t) = cong -_ (balance-is-≈-invariant s≈t)

0≢1 : ¬ (+ 0 ≡ + 1)
0≢1 = λ ()

e≉x : ¬ (e ≈ x)
e≉x (e≈x) = 0≢1 (balance-is-≈-invariant e≈x)

first-is-e-or-⁻¹ : notGp → Bool
first-is-e-or-⁻¹ e = true
first-is-e-or-⁻¹ x = false
first-is-e-or-⁻¹ (s ✶ t) = first-is-e-or-⁻¹ s
first-is-e-or-⁻¹ (s ⁻¹) = true

fieoi-is-≈-invariant : first-is-e-or-⁻¹ Preserves _≈_ ⟶ _≡_
fieoi-is-≈-invariant refl = ≡-refl
fieoi-is-≈-invariant (sym t≈s) = ≡-sym (fieoi-is-≈-invariant t≈s)
fieoi-is-≈-invariant (trans s≈u u≈t) = ≡-trans (fieoi-is-≈-invariant s≈u) (fieoi-is-≈-invariant u≈t)
fieoi-is-≈-invariant (assoc s t u) = ≡-refl
fieoi-is-≈-invariant (rightId s) = ≡-refl
fieoi-is-≈-invariant (leftInv s) = ≡-refl
fieoi-is-≈-invariant (✶-cong s≈t s′≈t′) = fieoi-is-≈-invariant s≈t
fieoi-is-≈-invariant (⁻¹-cong s≈t) = ≡-refl

true≢false : ¬ (true ≡ false)
true≢false = λ ()

e✶x≉x : ¬ (e ✶ x ≈ x)
e✶x≉x e✶x≈x = true≢false (fieoi-is-≈-invariant e✶x≈x)

-- There exists a wronggp that is not a gp.

wrongGpNotGp : ∃ {A = WrongGp Level.zero Level.zero} (λ W →
  (∃ (λ x → ¬ (e ✶ x ≈ x))))
wrongGpNotGp = NotGp , (x , e✶x≉x)
