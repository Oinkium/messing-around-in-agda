module WS-Strats where

open import Data.Empty
open import Data.Maybe
open import Data.Sum
open import Data.Function
open import Data.Unit
open import Data.Bool renaming
              (true to -   ;
               false to +  ;
               Bool to Pol ;
               T to IsTrue )
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import WS-Syn
open import WS-Rev
open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_ )
open import WS-Sem
open import WS-Comp

-- Extensional equality for Strategies

data _x=_ : ∀ {A} {p} → Strat p A → Strat p A → Set where
  pos : ∀ {G} i {f g : Strat - (G ▸ i)} →
        f x= g → _x=_ {G} (pos i f) (pos i g)
  neg : ∀ {G} {f g : (i : Mov G) → Strat + (G ▸ i)} →
        ((i : Mov G) → f i x= g i) → _x=_ {G} (neg f) (neg g)

-- Extending to bisimilar games

reflx= : ∀ {p} {A} (σ : Strat p A) → σ x= σ
reflx= (pos i y) = pos i (reflx= y)
reflx= (neg y) = neg (λ i → reflx= (y i))

clm1 : ∀ {p G} (σ : Strat p G) →
         unσ⊸o (σ⊸o σ) ≡ subst (λ p → Strat p G) (sym idem¬) σ
clm1 { + } {gam g} (pos i y) = refl
clm1 { - } {gam g} (neg y)   = refl

clm2 : ∀ {M N} (σ : Strat - M) (τ : Strat - N) → pi1 (σ σ& τ) ≡ σ
clm2 {gam m} {gam n} (neg y) (neg y') = refl

clm3 : ∀ {M N} (σ : Strat - M) (τ : Strat - N) → pi2 (σ σ& τ) ≡ τ
clm3 {gam m} {gam n} (neg y) (neg y') = refl

clm4 : ∀ {M N} (σ : Strat - (M ×' N)) → ((pi1 σ) σ& (pi2 σ)) x= σ
clm4 {gam m} {gam n} (neg y)
   = neg ([_,_] (λ m' → reflx= $ y $ inj₁ m') (λ n' → reflx= $ y $ inj₂ n'))

clm5 : ∀ {P} Q (σ : Strat + P) → coprod (σ⊕1 Q σ) ≡ inj₁ σ
clm5 {gam x} (gam y) (pos i f) = refl

clm6 : ∀ {P} Q (σ : Strat + P) → coprod (σ⊕2 Q σ) ≡ inj₂ σ
clm6 {gam x} (gam y) (pos i f) = refl

clm7 : ∀ {P Q} (σ : Strat + (P ×' Q))
    → [_,_] {Strat + P} {Strat + Q} {λ _ → Strat + (P ×' Q)}
         (σ⊕1 Q) (σ⊕2 P) (coprod σ) ≡ σ
clm7 {gam p} {gam q} (pos (inj₁ x) f) = refl
clm7 {gam p} {gam q} (pos (inj₂ y) f) = refl

clm8 : ∀ {Γ} {A : Fml +} → (σ : Strat + (⟦ Γ ⟧+ ⟦ A ⟧)) →
         (cast+ {Γ} {A} (cast+' {Γ} σ)) ≡ σ
clm8 {Γ} {A} (pos i y) with ⟦ Γ ⟧+ ⟦ A ⟧ | ⟦⟧ag+ A Γ
clm8 {Γ} {A} (pos i y)   | .(⟦ A , Γ ⟧') | refl = refl

clm8' : ∀ {Γ} {A : Fml +} → (σ : Strat + ⟦ A , Γ ⟧') →
         (cast+' {Γ} {A} (cast+ {Γ} σ)) ≡ σ
clm8' {Γ} {A} (pos i y) with ⟦ A , Γ ⟧' | ⟦⟧ag+ A Γ
...                   | .(⟦ Γ ⟧+ ⟦ A ⟧) | refl = refl

clm9 : ∀ {Γ} {A : Fml - } → (σ : Strat - (⟦ Γ ⟧- ⟦ A ⟧)) →
         (cast- {Γ} {A} (cast-' {Γ} σ)) ≡ σ
clm9 {Γ} {A} (neg f) with ⟦ Γ ⟧- ⟦ A ⟧ | ⟦⟧ag- A Γ
clm9 {Γ} {A} (neg f)   | .(⟦ A , Γ ⟧') | refl = refl

clm9' : ∀ {Γ} {A : Fml - } → (σ : Strat - ⟦ A , Γ ⟧') →
         (cast-' {Γ} {A} (cast- {Γ} σ)) ≡ σ
clm9' {Γ} {A} (neg f) with ⟦ A , Γ ⟧' | ⟦⟧ag- A Γ
...                   | .(⟦ Γ ⟧- ⟦ A ⟧) | refl = refl

clm10 : ∀ {Γ P Q} → (σ : Strat - (⟦ Γ ⟧- (P ×' Q))) → dec-' {Γ} (dec- {Γ} σ) ≡ σ
clm10 {Γ} {P} {Q} σ = {!!}


_inv_ : ∀ {A B} → (A → B) → (B → A) → Set
f inv g = (∀ a → f (g a) ≡ a) × (∀ a → g (f a) ≡ a)

_is≅ : ∀ {A B} → A ≈ B → Set
_is≅ {A} {B} (bsm (sim f g) (sim f' g')) = f inv f'


{-
dec- : ∀ {Γ P Q} → Strat - (⟦ Γ ⟧- (P ×' Q)) → Strat - (⟦ Γ ⟧- P ×' ⟦ Γ ⟧- Q)
dec- {Γ} {P} {Q} σ = spec (⟦≈×⟧- Γ P Q) σ

dec-' : ∀ {Γ P Q} → Strat - (⟦ Γ ⟧- P ×' ⟦ Γ ⟧- Q) → Strat - (⟦ Γ ⟧- (P ×' Q))
dec-' {Γ} {P} {Q} σ = spec (sym≈ $ ⟦≈×⟧- Γ P Q) σ

⟦≈×⟧- : ∀ Γ M N →  ⟦ Γ ⟧- (M ×' N) ≈ ⟦ Γ ⟧- M ×' ⟦ Γ ⟧- N
⟦≈×⟧- ε M N               = refl≈ (M ×' N)
⟦≈×⟧- (_,_ { - } O Γ) M N = tran≈ (Γ≈- Γ $ dist1 M N ⟦ O ⟧)
                                 (⟦≈×⟧- Γ (M ⊘' ⟦ O ⟧) (N ⊘' ⟦ O ⟧))
⟦≈×⟧- (_,_ { + } P Γ) M N = tran≈ (Γ≈- Γ $ dist2 M N ⟦ P ⟧)
                                 (⟦≈×⟧- Γ (⟦ P ⟧ ⊸ M) (⟦ P ⟧ ⊸ N))
-}

{-

cast+ : ∀ {Γ} {A : Fml +} → Strat + ⟦ A , Γ ⟧' → Strat + (⟦ Γ ⟧+ ⟦ A ⟧)
cast+ {Γ} {A} σ = subst (Strat +) (sym $ ⟦⟧ag+ A Γ) σ

cast+' : ∀ {Γ} {A : Fml +} → Strat + (⟦ Γ ⟧+ ⟦ A ⟧) → Strat + ⟦ A , Γ ⟧'
cast+' {Γ} {A} σ = subst (Strat +) (⟦⟧ag+ A Γ) σ

cast- : ∀ {Γ} {A : Fml - } → Strat - ⟦ A , Γ ⟧' → Strat - (⟦ Γ ⟧- ⟦ A ⟧)
cast- {Γ} {A} σ = subst (Strat -) (sym $ ⟦⟧ag- A Γ) σ

cast-' : ∀ {Γ} {A : Fml - } → Strat - (⟦ Γ ⟧- ⟦ A ⟧) → Strat - (⟦ A , Γ ⟧')
cast-' {Γ} {A} σ = subst (Strat -) (⟦⟧ag- A Γ) σ

cast+₂ : ∀ {Γ} {A : Fml +} {p} {B : Fml p} →
         Strat + ⟦ A , B , Γ ⟧' → Strat + (⟦ Γ ⟧+ ⟦ A , (B , ε) ⟧')
cast+₂ {Γ} {A} {p} {B} σ = subst (Strat +) (sym $ ⟦⟧ag+' A B Γ) σ

cast+'₂ : ∀ {Γ} {A : Fml +} {p} {B : Fml p} →
         Strat + (⟦ Γ ⟧+ ⟦ A , (B , ε) ⟧') → Strat + ⟦ A , B , Γ ⟧'
cast+'₂ {Γ} {A} {p} {B} σ = subst (Strat +) (⟦⟧ag+' A B Γ) σ

cast-₂ : ∀ {Γ} {A : Fml - } {p} {B : Fml p} →
         Strat - ⟦ A , B , Γ ⟧' → Strat - (⟦ Γ ⟧- ⟦ A , (B , ε) ⟧')
cast-₂ {Γ} {A} {p} {B} σ = subst (Strat -) (sym $ ⟦⟧ag-' A B Γ) σ

cast-'₂ : ∀ {Γ} {A : Fml - } {p} {B : Fml p} →
         Strat - (⟦ Γ ⟧- ⟦ A , B , ε ⟧') → Strat - (⟦ A , B , Γ ⟧')
cast-'₂ {Γ} {A} {p} {B} σ = subst (Strat -) (⟦⟧ag-' A B Γ) σ

dec+ : ∀ {Γ P Q} → Strat + (⟦ Γ ⟧+ (P ×' Q)) → Strat + (⟦ Γ ⟧+ P ×' ⟦ Γ ⟧+ Q)
dec+ {Γ} {P} {Q} σ = spec (⟦≈×⟧+ Γ P Q) σ

dec+' : ∀ {Γ P Q} → Strat + (⟦ Γ ⟧+ P ×' ⟦ Γ ⟧+ Q) → Strat + (⟦ Γ ⟧+ (P ×' Q))
dec+' {Γ} {P} {Q} σ = spec (sym≈ $ ⟦≈×⟧+ Γ P Q) σ

dec- : ∀ {Γ P Q} → Strat - (⟦ Γ ⟧- (P ×' Q)) → Strat - (⟦ Γ ⟧- P ×' ⟦ Γ ⟧- Q)
dec- {Γ} {P} {Q} σ = spec (⟦≈×⟧- Γ P Q) σ

dec-' : ∀ {Γ P Q} → Strat - (⟦ Γ ⟧- P ×' ⟦ Γ ⟧- Q) → Strat - (⟦ Γ ⟧- (P ×' Q))
dec-' {Γ} {P} {Q} σ = spec (sym≈ $ ⟦≈×⟧- Γ P Q) σ

Γis+ : ∀ {Γ M N} → M ≈ N → Strat + (⟦ Γ ⟧+ M) → Strat + (⟦ Γ ⟧+ N)
Γis+ {Γ} {M} {N} r σ = spec (Γ≈+ Γ r) σ

Γis- : ∀ {Γ M N} → M ≈ N → Strat - (⟦ Γ ⟧- M) → Strat - (⟦ Γ ⟧- N)
Γis- {Γ} {M} {N} r σ = spec (Γ≈- Γ r) σ

P1s : ∀ {Γ} → Strat - (⟦ Γ ⟧- I)
P1s {Γ} = spec (sym≈ (⟦≈1⟧- Γ)) σI

Γ× : ∀ {Γ M N} → Strat - (⟦ Γ ⟧- M) → Strat - (⟦ Γ ⟧- N) →
            Strat - (⟦ Γ ⟧- (M ×' N))
Γ× {Γ} {M} {N} σ τ = spec (sym≈ $ ⟦≈×⟧- Γ M N) (σ σ& τ)

Γi1 : ∀ {Γ Q P} → Strat + (⟦ Γ ⟧+ P) → Strat + (⟦ Γ ⟧+ (P ×' Q))
Γi1 {Γ} {Q} {P} σ = spec (sym≈ $ ⟦≈×⟧+ Γ P Q) $ σ⊕1 (⟦ Γ ⟧+ Q) σ

Γi2 : ∀ {Γ P Q} → Strat + (⟦ Γ ⟧+ Q) → Strat + (⟦ Γ ⟧+ (P ×' Q))
Γi2 {Γ} {P} {Q} σ = spec (sym≈ $ ⟦≈×⟧+ Γ P Q) $ σ⊕2 (⟦ Γ ⟧+ P) σ

clma8 : ∀ {Γ} {M N : Fml - } → (σ : Strat - ⟦ M , Γ ⟧')
           → (τ : Strat - ⟦ N , Γ ⟧') → un⟦P&1⟧ {Γ} (⟦P&⟧ {Γ} σ τ) x= σ
clma8 = ?


⟦P&⟧ : ∀ {Γ M N} →
      Strat - ⟦ M , Γ ⟧' → Strat - ⟦ N , Γ ⟧' → Strat - ⟦ M & N , Γ ⟧'
⟦P&⟧ {Γ} σ τ = cast-' {Γ} $ dec-' {Γ} $ (cast- {Γ} σ) σ& (cast- {Γ} τ)

un⟦P&1⟧ : ∀ {Γ M N} → Strat - ⟦ M & N , Γ ⟧' → Strat - ⟦ M , Γ ⟧'
un⟦P&1⟧ {Γ} σ = cast-' {Γ} $ pi1 $ dec- {Γ} $ cast- {Γ} $ σ

un⟦P&2⟧ : ∀ {Γ M N} → Strat - ⟦ M & N , Γ ⟧' → Strat - ⟦ N , Γ ⟧'
un⟦P&2⟧ {Γ} σ = cast-' {Γ} $ pi2 $ dec- {Γ} $ cast- {Γ} $ σ

clm1 σ with σ⊸o σ
clm1 { + }{G} (pos i y) | neg {.(gam (λ tt' → G))} y' = {!!}
clm1 { - } {G} (neg y)   | r = {!!}



σ⊸o : ∀ {p G} → Strat p G → Strat (not p) (G ⊸o)
σ⊸o { - } {gam g} σ = pos tt     σ
σ⊸o { + } {gam g} σ = neg (λ x → σ)

unσ⊸o : ∀ {p G} → Strat p (G ⊸o) → Strat (not p) G
unσ⊸o { - } {gam g} (neg f)    = f tt
unσ⊸o { + } {gam g} (pos tt τ) = τ

-}


