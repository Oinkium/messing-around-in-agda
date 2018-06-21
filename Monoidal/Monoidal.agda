module Monoidal where

open import Relation.Binary.PropositionalEquality

record Category : Set₁ where
  infixl 5 _∶_
  field
    Ob : Set
    _⟶_ : Ob → Ob → Set
    id : {A : Ob} → A ⟶ A
    _∶_ : {A B C : Ob} → A ⟶ B → B ⟶ C → A ⟶ C
    lunit : {A B : Ob} {f : A ⟶ B} → id ∶ f ≡ f
    runit : {A B : Ob} {f : A ⟶ B} → f ∶ id ≡ f
    assoc : {A B C D : Ob} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} → f ∶ (g ∶ h) ≡ (f ∶ g) ∶ h

Ob : Category → Set
Ob = Category.Ob

_[_,_] : (𝒞 : Category) → Ob 𝒞 → Ob 𝒞 → Set
𝒞 [ A , B ] = Category._⟶_ 𝒞 A B

_∶_ : {𝒞 : Category} {A B C : Ob 𝒞} → 𝒞 [ A , B ] → 𝒞 [ B , C ] → 𝒞 [ A , C ]
_∶_ {𝒞} {A} {B} {C} f g = Category._∶_ 𝒞 f g

_-_⟶_-_⟶_ : {𝒞 : Category} (A : Ob 𝒞) {B : Ob 𝒞} (f : 𝒞 [ A , B ]) (B : Ob 𝒞) {C : Ob 𝒞} (g : 𝒞 [ B , C ]) (C : Ob 𝒞) → 𝒞 [ A , B ]
A - f ⟶ B - g ⟶ C = f ∶ g

record Functor : Set₁ where
  field
    source : Category
    target : Category
    onObjects : Ob source → Ob target
    onMorphisms : {A B : Ob source} → source [ A , B ] → target [ (onObjects A) , (onObjects B) ]
    preservesComposition : {A B C : Ob source} {f : source [ A , B ]} {g : source [ B , C ]} → onMorphisms(f ∶ g) ≡ (onMorphisms f) ∶ (onMorphisms g)

record MonoidalCategory : Set₁ where
  field
    Carrier : Category
