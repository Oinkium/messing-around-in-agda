module WrongGp where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import Data.Bool
open import Data.Product

open import Algebra.Structures

import Algebra.FunctionProperties as FunctionProperties
open import Function
open import Level using (_⊔_; suc)

open FunctionProperties using (Op₁; Op₂)

record IsWrongGp {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                 (e : A) (⁻¹ : Op₁ A) (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isSemigroup : IsSemigroup ≈ ∙
    rightId     : RightIdentity e ∙
    ⁻¹-cong     : ⁻¹ Preserves ≈ ⟶ ≈
    leftInv     : LeftInverse e ⁻¹ ∙

record WrongGp c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 7 _∙_
  infix 4 _≈_
  field
    Carrier   : Set c
    _≈_       : Rel Carrier ℓ
    e         : Carrier
    _⁻¹       : Op₁ Carrier
    _∙_       : Op₂ Carrier
    isWrongGp : IsWrongGp _≈_ e _⁻¹ _∙_

infix 7 _∙_
infix 4 _≈_

data notGpBase : Set where
  e   : notGpBase
  x   : notGpBase
  _⁻¹ : Op₁ notGpBase
  _∙_ : Op₂ notGpBase

open FunctionProperties

data _≈_  : Rel notGpBase Level.zero where
  refl    : Reflexive _≈_
  sym     : Symmetric _≈_
  trans   : Transitive _≈_
  assoc   : Associative _≈_ _∙_
  ∙-cong  : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  rightId : RightIdentity _≈_ e _∙_
  ⁻¹-cong : _⁻¹ Preserves _≈_ ⟶ _≈_
  leftInv : LeftInverse _≈_ e _⁻¹ _∙_

notGp : WrongGp Level.zero Level.zero
notGp = record {
  Carrier   = notGpBase;
  _≈_       = _≈_;
  e         = e;
  _⁻¹       = _⁻¹;
  _∙_       = _∙_;
  isWrongGp = record {
    isSemigroup = record {
      isEquivalence = record {
        refl  = refl;
        sym   = sym;
        trans = trans};
      assoc  = assoc;
      ∙-cong = ∙-cong};
    rightId = rightId;
    ⁻¹-cong = ⁻¹-cong;
    leftInv = leftInv}}

starts-with-x : notGpBase → Bool
starts-with-x e       = false
starts-with-x x       = true
starts-with-x (s ⁻¹)  = false
starts-with-x (s ∙ t) = starts-with-x s

starts-with-x-is-≈-invariant : starts-with-x Preserves _≈_ ⟶ _≡_
starts-with-x-is-≈-invariant refl = ≡-refl
starts-with-x-is-≈-invariant (sym t≈s) = ≡-sym (starts-with-x-is-≈-invariant t≈s)
starts-with-x-is-≈-invariant (trans s≈u u≈t) = ≡-trans (starts-with-x-is-≈-invariant s≈u) (starts-with-x-is-≈-invariant u≈t)
starts-with-x-is-≈-invariant (assoc s t u) = ≡-refl
starts-with-x-is-≈-invariant (∙-cong s≈t s′≈t′) = starts-with-x-is-≈-invariant s≈t
starts-with-x-is-≈-invariant (rightId s) = ≡-refl
starts-with-x-is-≈-invariant (⁻¹-cong s≈t) = ≡-refl
starts-with-x-is-≈-invariant (leftInv s) = ≡-refl

true≢false : ¬ (true ≡ false)
true≢false = λ ()

x≉e∙x : ¬ (x ≈ e ∙ x)
x≉e∙x x≈e∙x = true≢false (starts-with-x-is-≈-invariant x≈e∙x)

x∙x⁻¹≉e : ¬ (x ∙ (x ⁻¹) ≈ e)
x∙x⁻¹≉e x∙x⁻¹≈e = true≢false (starts-with-x-is-≈-invariant x∙x⁻¹≈e)

not-every-wrongGp-is-a-gp : ∃ {A = WrongGp Level.zero Level.zero}
  (λ W → ∃ (λ y → (¬ (y ≈ e ∙ y)) × (¬ (y ∙ (y ⁻¹) ≈ e))))
not-every-wrongGp-is-a-gp = notGp , (x , (x≉e∙x , x∙x⁻¹≉e))
