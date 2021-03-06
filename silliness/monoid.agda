module monoid where

data List (A : Set) : Set where
  emptyList : List A
  append : List A -> (A -> List A)

concatenate : {A : Set} -> (List A -> (List A -> List A))
concatenate L emptyList = L
concatenate L (append M a) = append (concatenate L M) a

_* : {A : Set} -> {B : Set} -> ((A -> B) -> (List A -> List B))
(f *) emptyList = emptyList
(f *) (append L a) = append ((f *) L) (f a)

FreeMonoidSet : Set -> Set
FreeMonoidSet A = List A

MonadAction : {A : Set} -> (FreeMonoidSet (FreeMonoidSet A) -> FreeMonoidSet A)
MonadAction emptyList = emptyList
MonadAction (append M a) = concatenate (MonadAction M) a

PreMonoid : {A : Set} -> Set
PreMonoid {A} = (FreeMonoidSet A) -> A

data _≡_ {X} : X -> (X -> Set) where
  refl : (x : X) -> x ≡ x

AssociativityProof : {A : Set} -> {PreMonoid {A}} -> Set
AssociativityProof {PM} = (λ 𝔏 -> PM (MonadAction 𝔏)) ≡ (λ 𝔏 -> PM ((PM *) 𝔏))

FreeMonoid : (A : Set) -> PreMonoid {FreeMonoidSet A}
FreeMonoid A L = MonadAction {A} L

FreeMonoidAssociativity : (A : Set) -> AssociativityProof {FreeMonoidSet A}
FreeMonoidAssociativity A = refl (λ 𝓛 -> MonadAction (MonadAction 𝓛)) (λ 𝓛 -> MonadAction ((MonadAction *) 𝓛))


