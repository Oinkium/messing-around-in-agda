module WS-Sem-Core where

open import Data.Bool renaming (true to - ; false to +; Bool to Pol)
open import Data.Function
open import Data.Sum
open import Relation.Binary.PropositionalEquality

open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import WS-Syn

-- Semantics of WS

-- Formulas and sequents

⟦_⟧ : {p : Pol} → Fml p → Game
⟦   F1  ⟧         = I
⟦  ↑ P  ⟧         = ⟦ P ⟧ ⊸o
⟦   F0  ⟧         = I
⟦  ↓ N  ⟧         = ⟦ N ⟧ ⊸o
⟦ M ⊗ N ⟧         = ⟦ M ⟧ ⊗' ⟦ N ⟧
⟦ P ⅋ Q ⟧         = ⟦ P ⟧ ⊗' ⟦ Q ⟧
⟦ M & N ⟧         = ⟦ M ⟧ ×' ⟦ N ⟧
⟦ P ⊕ Q ⟧         = ⟦ P ⟧ ×' ⟦ Q ⟧
⟦ _⊘_ { - } M N ⟧ = ⟦ M ⟧ ⊘' ⟦ N ⟧ 
⟦ _⊘_ { + } P N ⟧ = ⟦ N ⟧ ⊸ ⟦ P ⟧
⟦ _◁_ { + } P Q ⟧ = ⟦ P ⟧ ⊘' ⟦ Q ⟧ 
⟦ _◁_ { - } M P ⟧ = ⟦ P ⟧ ⊸ ⟦ M ⟧

_F : ∀ {p} → Seq p → Fml p
_F (A , ε)               = A
_F (A , (_,_ { - } M Γ)) = (A ⊘ M , Γ) F
_F (A , (_,_ { + } P Γ)) = (A ◁ P , Γ) F

⟦_⟧' : ∀ {p} → Seq p → Game
⟦ Γ ⟧' = ⟦ Γ F ⟧

-- Contexts as Functors

⟦_⟧- : Ctx → Game → Game
⟦ ε ⟧-             G = G
⟦ _,_ { - } M Γ ⟧- G = ⟦ Γ ⟧- (G ⊘' ⟦ M ⟧ )
⟦ _,_ { + } P Γ ⟧- G = ⟦ Γ ⟧- (⟦ P ⟧ ⊸ G)

⟦_⟧+ : Ctx → Game → Game
⟦ ε ⟧+             G = G
⟦ _,_ { + } P Γ ⟧+ G = ⟦ Γ ⟧+ (G ⊘' ⟦ P ⟧)
⟦ _,_ { - } M Γ ⟧+ G = ⟦ Γ ⟧+ (⟦ M ⟧ ⊸ G)

⟦_⟧≲-_ : ∀ {M N} Γ → M ≲ N → ⟦ Γ ⟧- M ≲ ⟦ Γ ⟧- N
⟦ ε ⟧≲-             c = c
⟦ _,_ { + } P Γ ⟧≲- c = ⟦ Γ ⟧≲- (⟦ P ⟧ ⊸≲ c)
⟦ _,_ { - } O Γ ⟧≲- c = ⟦ Γ ⟧≲- (c ≲⊘ ⟦ O ⟧)

⟦_⟧≲+_ : ∀ {M N} Γ → M ≲ N → (⟦ Γ ⟧+ M) ≲ (⟦ Γ ⟧+ N)
⟦ ε ⟧≲+             c = c
⟦ _,_ { - } O Γ ⟧≲+ c = ⟦ Γ ⟧≲+ (⟦ O ⟧ ⊸≲ c)
⟦ _,_ { + } P Γ ⟧≲+ c = ⟦ Γ ⟧≲+ (c ≲⊘ ⟦ P ⟧)

⟦_⟧≈-_ : ∀ {M N} Γ → M ≈ N → (⟦ Γ ⟧- M) ≈ (⟦ Γ ⟧- N)
⟦ ε ⟧≈-             c = c
⟦ _,_ { + } P Γ ⟧≈- c = ⟦ Γ ⟧≈- (⟦ P ⟧ ⊸≈ c)
⟦ _,_ { - } O Γ ⟧≈- c = ⟦ Γ ⟧≈- (c ≈⊘ ⟦ O ⟧)

⟦_⟧≈+ : ∀ {M N} Γ → M ≈ N → (⟦ Γ ⟧+ M) ≈ (⟦ Γ ⟧+ N)
⟦ ε ⟧≈+             c = c
⟦ _,_ { - } O Γ ⟧≈+ c = ⟦ Γ ⟧≈+ (⟦ O ⟧ ⊸≈ c)
⟦ _,_ { + } P Γ ⟧≈+ c = ⟦ Γ ⟧≈+ (c ≈⊘ ⟦ P ⟧)

⟦,x⟧is⟦x⟧- : ∀ {M : Fml - } Γ → ⟦ Γ ⟧- ⟦ M ⟧ ≡ ⟦ M , Γ ⟧'
⟦,x⟧is⟦x⟧- ε               = refl
⟦,x⟧is⟦x⟧- (_,_ { - } _ Γ) = ⟦,x⟧is⟦x⟧- Γ
⟦,x⟧is⟦x⟧- (_,_ { + } _ Γ) = ⟦,x⟧is⟦x⟧- Γ

⟦,x⟧is⟦x⟧+ : ∀ {P : Fml +} Γ → ⟦ Γ ⟧+ ⟦ P ⟧ ≡ ⟦ P , Γ ⟧'
⟦,x⟧is⟦x⟧+ ε               = refl
⟦,x⟧is⟦x⟧+ (_,_ { - } _ Γ) = ⟦,x⟧is⟦x⟧+ Γ
⟦,x⟧is⟦x⟧+ (_,_ { + } _ Γ) = ⟦,x⟧is⟦x⟧+ Γ

⟦,x⟧is⟦x⟧+' : ∀ {p} (P : Fml +) (A : Fml p) Γ
        → ⟦ Γ ⟧+ ⟦ P , A , ε ⟧' ≡ ⟦ P , A , Γ ⟧'
⟦,x⟧is⟦x⟧+' P A ε                      = refl
⟦,x⟧is⟦x⟧+' { + } P Ap (_,_ { + } Q Γ) = ⟦,x⟧is⟦x⟧+' (P ◁ Ap) Q Γ
⟦,x⟧is⟦x⟧+' { + } P Ap (_,_ { - } N Γ) = ⟦,x⟧is⟦x⟧+' (P ◁ Ap) N Γ
⟦,x⟧is⟦x⟧+' { - } P An (_,_ { - } N Γ) = ⟦,x⟧is⟦x⟧+' (P ⊘ An) N Γ
⟦,x⟧is⟦x⟧+' { - } P An (_,_ { + } Q Γ) = ⟦,x⟧is⟦x⟧+' (P ⊘ An) Q Γ

⟦,x⟧is⟦x⟧-' : ∀ {p} (M : Fml -) (A : Fml p) Γ
        → ⟦ Γ ⟧- ⟦ M , A , ε ⟧' ≡ ⟦ M , A , Γ ⟧'
⟦,x⟧is⟦x⟧-' M A ε                      = refl
⟦,x⟧is⟦x⟧-' { + } M Ap (_,_ { + } Q Γ) = ⟦,x⟧is⟦x⟧-' (M ◁ Ap) Q Γ
⟦,x⟧is⟦x⟧-' { + } M Ap (_,_ { - } N Γ) = ⟦,x⟧is⟦x⟧-' (M ◁ Ap) N Γ
⟦,x⟧is⟦x⟧-' { - } M An (_,_ { - } N Γ) = ⟦,x⟧is⟦x⟧-' (M ⊘ An) N Γ
⟦,x⟧is⟦x⟧-' { - } M An (_,_ { + } Q Γ) = ⟦,x⟧is⟦x⟧-' (M ⊘ An) Q Γ

-- Context distributivity isomorphisms

Γ-I≈I : ∀ Γ → ⟦ Γ ⟧- I ≈ I
Γ-I≈I ε               = id≈
Γ-I≈I (_,_ { - } _ Γ) = (⟦ Γ ⟧≈- dist01) ∘≈ (Γ-I≈I Γ)
Γ-I≈I (_,_ { + } _ Γ) = (⟦ Γ ⟧≈- dist02) ∘≈ (Γ-I≈I Γ)

distΓ- : ∀ Γ {M N} →  ⟦ Γ ⟧- (M ×' N) ≈ ⟦ Γ ⟧- M ×' ⟦ Γ ⟧- N
distΓ- ε               = id≈
distΓ- (_,_ { - } _ Γ) = (⟦ Γ ⟧≈- dist1) ∘≈ (distΓ- Γ)
distΓ- (_,_ { + } _ Γ) = (⟦ Γ ⟧≈- dist2) ∘≈ (distΓ- Γ)

distΓ+ : ∀ Γ {M N} →  ⟦ Γ ⟧+ (M ×' N) ≈ ⟦ Γ ⟧+ M ×' ⟦ Γ ⟧+ N
distΓ+ ε               = id≈
distΓ+ (_,_ { + } _ Γ) = (⟦ Γ ⟧≈+ dist1) ∘≈ distΓ+ Γ
distΓ+ (_,_ { - } _ Γ) = (⟦ Γ ⟧≈+ dist2) ∘≈ distΓ+ Γ

-- Casting strategies

cast+ : ∀ {Γ} {A : Fml +} → Strat + ⟦ A , Γ ⟧' → Strat + (⟦ Γ ⟧+ ⟦ A ⟧)
cast+ {Γ} σ = subst (Strat +) (sym $ ⟦,x⟧is⟦x⟧+ Γ) σ

cast+' : ∀ {Γ} {A : Fml +} → Strat + (⟦ Γ ⟧+ ⟦ A ⟧) → Strat + ⟦ A , Γ ⟧'
cast+' {Γ} σ = subst (Strat +) (⟦,x⟧is⟦x⟧+ Γ) σ

cast- : ∀ {Γ} {A : Fml - } → Strat - ⟦ A , Γ ⟧' → Strat - (⟦ Γ ⟧- ⟦ A ⟧)
cast- {Γ} σ = subst (Strat -) (sym $ ⟦,x⟧is⟦x⟧- Γ) σ

cast-' : ∀ {Γ} {A : Fml - } → Strat - (⟦ Γ ⟧- ⟦ A ⟧) → Strat - (⟦ A , Γ ⟧')
cast-' {Γ} σ = subst (Strat -) (⟦,x⟧is⟦x⟧- Γ) σ

cast+₂ : ∀ {Γ} {A : Fml +} {p} {B : Fml p} →
         Strat + ⟦ A , B , Γ ⟧' → Strat + (⟦ Γ ⟧+ ⟦ A , (B , ε) ⟧')
cast+₂ {Γ} {A} {_} {B} σ = subst (Strat +) (sym $ ⟦,x⟧is⟦x⟧+' A B Γ) σ

cast+'₂ : ∀ {Γ} {A : Fml +} {p} {B : Fml p} →
         Strat + (⟦ Γ ⟧+ ⟦ A , (B , ε) ⟧') → Strat + ⟦ A , B , Γ ⟧'
cast+'₂ {Γ} {A} {_} {B} σ = subst (Strat +) (⟦,x⟧is⟦x⟧+' A B Γ) σ

cast-₂ : ∀ {Γ} {A : Fml - } {p} {B : Fml p} →
         Strat - ⟦ A , B , Γ ⟧' → Strat - (⟦ Γ ⟧- ⟦ A , (B , ε) ⟧')
cast-₂ {Γ} {A} {_} {B} σ = subst (Strat -) (sym $ ⟦,x⟧is⟦x⟧-' A B Γ) σ

cast-'₂ : ∀ {Γ} {A : Fml - } {p} {B : Fml p} →
         Strat - (⟦ Γ ⟧- ⟦ A , B , ε ⟧') → Strat - (⟦ A , B , Γ ⟧')
cast-'₂ {Γ} {A} {_} {B} σ = subst (Strat -) (⟦,x⟧is⟦x⟧-' A B Γ) σ

Γ≈σ+ : ∀ {Γ M N} → M ≈ N → Strat + (⟦ Γ ⟧+ M) → Strat + (⟦ Γ ⟧+ N)
Γ≈σ+ {Γ} r σ = spec (⟦ Γ ⟧≈+ r) σ

Γ≈σ- : ∀ {Γ M N} → M ≈ N → Strat - (⟦ Γ ⟧- M) → Strat - (⟦ Γ ⟧- N)
Γ≈σ- {Γ} r σ = spec (⟦ Γ ⟧≈- r) σ

-- Pulling products out of contexts

dec+ : ∀ {Γ P Q} → Strat + (⟦ Γ ⟧+ (P ×' Q)) → Strat + (⟦ Γ ⟧+ P ×' ⟦ Γ ⟧+ Q)
dec+ {Γ} σ = spec (distΓ+ Γ) σ

dec+' : ∀ {Γ P Q} → Strat + (⟦ Γ ⟧+ P ×' ⟦ Γ ⟧+ Q) → Strat + (⟦ Γ ⟧+ (P ×' Q))
dec+' {Γ} σ = spec (sym≈ $ distΓ+ Γ) σ

dec- : ∀ {Γ P Q} → Strat - (⟦ Γ ⟧- (P ×' Q)) → Strat - (⟦ Γ ⟧- P ×' ⟦ Γ ⟧- Q)
dec- {Γ} σ = spec (distΓ- Γ) σ

dec-' : ∀ {Γ P Q} → Strat - (⟦ Γ ⟧- P ×' ⟦ Γ ⟧- Q) → Strat - (⟦ Γ ⟧- (P ×' Q))
dec-' {Γ} σ = spec (sym≈ $ distΓ- Γ) σ

-- Distributivity and Strategies

P1s : ∀ {Γ} → Strat - (⟦ Γ ⟧- I)
P1s {Γ} = spec (sym≈ $ Γ-I≈I Γ) σI

Γ× : ∀ {Γ M N} → Strat - (⟦ Γ ⟧- M) → Strat - (⟦ Γ ⟧- N) →
            Strat - (⟦ Γ ⟧- (M ×' N))
Γ× {Γ} σ τ = spec (sym≈ $ distΓ- Γ) (σ σ& τ)

Γi1 : ∀ {Γ Q P} → Strat + (⟦ Γ ⟧+ P) → Strat + (⟦ Γ ⟧+ (P ×' Q))
Γi1 {Γ} {Q} {_} σ = spec (sym≈ $ distΓ+ Γ) $ σ⊕1 (⟦ Γ ⟧+ Q) σ

Γi2 : ∀ {Γ P Q} → Strat + (⟦ Γ ⟧+ Q) → Strat + (⟦ Γ ⟧+ (P ×' Q))
Γi2 {Γ} {P} {_} σ = spec (sym≈ $ distΓ+ Γ) $ σ⊕2 (⟦ Γ ⟧+ P) σ

-- Semantics of Proofs

⟦P1⟧ : ∀ {Γ} → Strat - ⟦ F1 , Γ ⟧'
⟦P1⟧ {Γ} = cast-' {Γ} $ P1s {Γ}

⟦P&⟧ : ∀ {Γ M N} →
      Strat - ⟦ M , Γ ⟧' → Strat - ⟦ N , Γ ⟧' → Strat - ⟦ M & N , Γ ⟧'
⟦P&⟧ {Γ} σ τ = cast-' {Γ} $ dec-' {Γ} $ (cast- {Γ} σ) σ& (cast- {Γ} τ)

⟦P⊗⟧ : ∀ {Γ M N} →
      Strat - ⟦ M , N , Γ ⟧' → Strat - ⟦ N , M , Γ ⟧' → Strat - ⟦ M ⊗ N , Γ ⟧'
⟦P⊗⟧ {Γ} {M} {N} σ τ
  = cast-' {Γ} $ Γ≈σ- {Γ} (sym≈ dec1) $ dec-' {Γ} $
     (cast-₂ {Γ} {M} { - } {N} σ) σ& (cast-₂ {Γ} {N} { - } {M} τ)

⟦P⊘⟧ : ∀ {Γ : Ctx}{p : Pol}{A : Fml p }{N : Fml - } →
      Strat p ⟦ A , N , Γ ⟧' → Strat p ⟦ A ⊘ N , Γ ⟧'
⟦P⊘⟧ σ = spec id≈ σ

⟦P◁⟧ : ∀ {Γ : Ctx}{p : Pol}{A : Fml p }{P : Fml + } →
      Strat p ⟦ A , P , Γ ⟧' → Strat p ⟦ A ◁ P , Γ ⟧'
⟦P◁⟧ σ = spec id≈ σ

⟦P⊕1⟧ : ∀ {Γ P Q} → Strat + ⟦ P , Γ ⟧' → Strat + ⟦ P ⊕ Q , Γ ⟧'
⟦P⊕1⟧ {Γ} {_} {Q} σ
  = cast+' {Γ} $ Γi1 {Γ} {⟦ Q ⟧} $ cast+ {Γ} σ

⟦P⊕2⟧ : ∀ {Γ P Q} → Strat + ⟦ Q , Γ ⟧' → Strat + ⟦ P ⊕ Q , Γ ⟧'
⟦P⊕2⟧ {Γ} {P} {_} σ
  = cast+' {Γ} $ Γi2 {Γ} {⟦ P ⟧} $ cast+ {Γ} σ

⟦P⅋1⟧ : ∀ {Γ P Q} → Strat + ⟦ P , Q , Γ ⟧' → Strat + ⟦ P ⅋ Q , Γ ⟧'
⟦P⅋1⟧ {Γ} {P} {Q} σ
  = cast+' {Γ} $ Γ≈σ+ {Γ} (sym≈ dec1) $ Γi1 {Γ} {⟦ Q ◁ P ⟧} $
    cast+₂ {Γ} {P} { + } {Q} σ

⟦P⅋2⟧ : ∀ {Γ P Q} → Strat + ⟦ Q , P , Γ ⟧' → Strat + ⟦ P ⅋ Q , Γ ⟧'
⟦P⅋2⟧ {Γ} {P} {Q} σ
  = cast+' {Γ} $ Γ≈σ+ {Γ} (sym≈ dec1) $ Γi2 {Γ} {⟦ P ◁ Q ⟧} $
    cast+₂ {Γ} {Q} { + } {P} σ

⟦P↑-⟧ : ∀ {Γ P N} → Strat - ⟦ ↑(P ⊘ N) , Γ ⟧' → Strat - ⟦ ↑ P , N , Γ ⟧'
⟦P↑-⟧ {Γ} {P} {N} σ
  = cast-'₂ {Γ} {↑ P} { - } {N} $ Γ≈σ- {Γ} lfe $ cast- {Γ} σ

⟦P↓+⟧ : ∀ {Γ N P} → Strat + ⟦ ↓(N ◁ P) , Γ ⟧' → Strat + ⟦ ↓ N , P , Γ ⟧'
⟦P↓+⟧ {Γ} {N} {P} σ
  = cast+'₂ {Γ} {↓ N} { + } {P} $ Γ≈σ+ {Γ} lfe $ cast+ {Γ} σ

⟦P↑+⟧ : ∀ {Γ P Q} → Strat - ⟦ ↑(P ⅋ Q) , Γ ⟧' → Strat - ⟦ ↑ P , Q , Γ ⟧'
⟦P↑+⟧ {Γ} {P} {Q} σ
  = cast-'₂ {Γ} {↑ P} { + } {Q} $ Γ≈σ- {Γ} curryo $ cast- {Γ} σ

⟦P↓-⟧ : ∀ {Γ M N} → Strat + ⟦ ↓(M ⊗ N) , Γ ⟧' → Strat + ⟦ ↓ M , N , Γ ⟧'
⟦P↓-⟧ {Γ} {M} {N} σ
  = cast+'₂ {Γ} {↓ M} { - } {N} $ Γ≈σ+ {Γ} curryo $ cast+ {Γ} σ

⟦P↑⟧ : ∀ {P} → Strat + ⟦ P , ε ⟧' → Strat - ⟦ ↑ P , ε ⟧'
⟦P↑⟧ σ = σ⊸o σ

⟦P↓⟧ : ∀ {N} → Strat - ⟦ N , ε ⟧' → Strat + ⟦ ↓ N , ε ⟧'
⟦P↓⟧ σ = σ⊸o σ

⟦_⟧⊢ : ∀ {p}{Γ : Seq p} → ⊢ Γ → Strat p ⟦ Γ ⟧'
⟦_⟧⊢ {Γ = F1 , Γ } P1           = ⟦P1⟧ {Γ}
⟦_⟧⊢ {Γ = M ⊗ N , Γ } (P⊗ y y') = ⟦P⊗⟧  {Γ} ⟦ y ⟧⊢ ⟦ y' ⟧⊢
⟦_⟧⊢ {Γ = P ⅋ Q , Γ } (P⅋₁ y)   = ⟦P⅋1⟧ {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = P ⅋ Q , Γ } (P⅋₂ y)   = ⟦P⅋2⟧ {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = P ⊕ Q , Γ } (P⊕₁ y)   = ⟦P⊕1⟧ {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = P ⊕ Q , Γ } (P⊕₂ y)   = ⟦P⊕2⟧ {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = M & N , Γ } (P& y y') = ⟦P&⟧  {Γ} ⟦ y ⟧⊢ ⟦ y' ⟧⊢
⟦_⟧⊢ {Γ = A ⊘ M , Γ } (P⊘ y)    = ⟦P⊘⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = A ◁ P , Γ } (P◁ y)    = ⟦P◁⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = ↑ P , ε } (P↑ y)      = ⟦P↑⟧  {P} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = ↑ P , M , Γ } (P↑- y) = ⟦P↑-⟧ {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = ↑ P , Q , Γ } (P↑+ y) = ⟦P↑+⟧ {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = ↓ N , ε } (P↓ y)      = ⟦P↓⟧  {N} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = ↓ N , P , Γ } (P↓+ y) = ⟦P↓+⟧ {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = ↓ N , M , Γ } (P↓- y) = ⟦P↓-⟧ {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {Γ = F0 , Γ } () 


-- Semantics of non-core proofs

,,F⊘ : ∀ {p} (Γ : Seq p ) M → (Γ ,,₂ M) F ≡ Γ F ⊘ M
,,F⊘ (M , ε) N = refl
,,F⊘ (M , (_,_ { - } O Γ)) N = ,,F⊘ (M ⊘ O , Γ) N
,,F⊘ (M , (_,_ { + } P Γ)) N = ,,F⊘ (M ◁ P , Γ) N

,,F◁ : ∀ {p} (Γ : Seq p ) M → (Γ ,,₂ M) F ≡ Γ F ◁ M
,,F◁ (M , ε) N = refl
,,F◁ (M , (_,_ { - } O Γ)) N = ,,F◁ (M ⊘ O , Γ) N
,,F◁ (M , (_,_ { + } P Γ)) N = ,,F◁ (M ◁ P , Γ) N

⟦,,₀⟧' : ∀ {p}(Γ : Seq p) Δ → ⟦ Γ F , Δ ⟧' ≡ ⟦ Γ ,,₀ Δ ⟧' 
⟦,,₀⟧' Γ ε with Γ ,,₀ ε | ,,₀ε Γ
...       | .Γ      | refl = refl
⟦,,₀⟧' { - } Γ (_,_ { - } M' Δ)
 with (Γ ,,₂ M') F | ,,F⊘ Γ M' | Γ ,,₀ (M' , Δ)
      | ,,₂₀ Γ M' Δ | ⟦,,₀⟧' (Γ ,,₂ M') Δ
...| .((Γ F) ⊘ M') | refl | .(Γ ,,₂ M' ,,₀ Δ) | refl | y = y
⟦,,₀⟧' { - } Γ (_,_ { + } M' Δ)
 with (Γ ,,₂ M') F | ,,F◁ Γ M' | Γ ,,₀ (M' , Δ)
      | ,,₂₀ Γ M' Δ | ⟦,,₀⟧' (Γ ,,₂ M') Δ
...| .((Γ F) ◁ M') | refl | .(Γ ,,₂ M' ,,₀ Δ) | refl | y = y
⟦,,₀⟧' { + } Γ (_,_ { - } M' Δ)
 with (Γ ,,₂ M') F | ,,F⊘ Γ M' | Γ ,,₀ (M' , Δ)
      | ,,₂₀ Γ M' Δ | ⟦,,₀⟧' (Γ ,,₂ M') Δ
...| .((Γ F) ⊘ M') | refl | .(Γ ,,₂ M' ,,₀ Δ) | refl | y = y
⟦,,₀⟧' { + } Γ (_,_ { + } M' Δ)
 with (Γ ,,₂ M') F | ,,F◁ Γ M' | Γ ,,₀ (M' , Δ)
      | ,,₂₀ Γ M' Δ | ⟦,,₀⟧' (Γ ,,₂ M') Δ
...| .((Γ F) ◁ M') | refl | .(Γ ,,₂ M' ,,₀ Δ) | refl | y = y

⟦,Δ⟧is⟦Δ⟧+ : ∀ (Γ : Seq +) Δ → ⟦ Δ ⟧+ ⟦ Γ ⟧' ≡ ⟦ Γ ,,₀ Δ ⟧'
⟦,Δ⟧is⟦Δ⟧+ Γ Δ with    ⟦ Γ F , Δ ⟧' | ⟦,,₀⟧' Γ Δ | ⟦,x⟧is⟦x⟧+ {Γ F} Δ
...              | .(⟦ Γ ,,₀ Δ ⟧') | refl   | x = x

⟦,Δ⟧is⟦Δ⟧- : ∀ (Γ : Seq -) Δ → ⟦ Δ ⟧- ⟦ Γ ⟧' ≡ ⟦ Γ ,,₀ Δ ⟧'
⟦,Δ⟧is⟦Δ⟧- Γ Δ with    ⟦ Γ F , Δ ⟧' | ⟦,,₀⟧' Γ Δ | ⟦,x⟧is⟦x⟧- {Γ F} Δ
...                  | .(⟦ Γ ,,₀ Δ ⟧') | refl   | x = x


cast+Γ : ∀ {Γ : Seq +} {Δ} → Strat + ⟦ Γ ,,₀ Δ ⟧' → Strat + (⟦ Δ ⟧+ ⟦ Γ ⟧')
cast+Γ {Γ} {Δ} σ = subst (Strat +) (sym $ ⟦,Δ⟧is⟦Δ⟧+ Γ Δ) σ

cast+'Γ : ∀ {Γ : Seq +} {Δ} → Strat + (⟦ Δ ⟧+ ⟦ Γ ⟧') → Strat + ⟦ Γ ,,₀ Δ ⟧'
cast+'Γ {Γ} {Δ} σ = subst (Strat +) (⟦,Δ⟧is⟦Δ⟧+ Γ Δ) σ

cast-Γ : ∀ {Γ : Seq - } {Δ} → Strat - ⟦ Γ ,,₀ Δ ⟧' → Strat - (⟦ Δ ⟧- ⟦ Γ ⟧')
cast-Γ {Γ} {Δ} σ = subst (Strat -) (sym $ ⟦,Δ⟧is⟦Δ⟧- Γ Δ) σ

cast-'Γ : ∀ {Γ : Seq - } {Δ} → Strat - (⟦ Δ ⟧- ⟦ Γ ⟧') → Strat - ⟦ Γ ,,₀ Δ ⟧'
cast-'Γ {Γ} {Δ} σ = subst (Strat -) (⟦,Δ⟧is⟦Δ⟧- Γ Δ) σ

⟦P1T⟧ : ∀ {p Δ}{Γ : Seq p} → Strat p ⟦ Γ ,,₀ Δ ⟧' → Strat p ⟦ Γ ,,₀ F1 , Δ ⟧'
⟦P1T⟧ { + } {Δ} {Γ} σ
   = cast+'Γ {Γ} {F1 , Δ} $ spec (⟦ Δ ⟧≈+ (sym≈ unit⊸)) $ cast+Γ {Γ} {Δ} σ
⟦P1T⟧ { - } {Δ} {Γ} σ
   = cast-'Γ {Γ} {F1 , Δ} $ spec (⟦ Δ ⟧≈- (sym≈ unit⊘)) $ cast-Γ {Γ} {Δ} σ

⟦P0T⟧ : ∀ {p Δ}{Γ : Seq p} → Strat p ⟦ Γ ,,₀ Δ ⟧' → Strat p ⟦ Γ ,,₀ F0 , Δ ⟧'
⟦P0T⟧ { + } {Δ} {Γ} σ
   = cast+'Γ {Γ} {F0 , Δ} $ spec (⟦ Δ ⟧≈+ (sym≈ unit⊘)) $ cast+Γ {Γ} {Δ} σ
⟦P0T⟧ { - } {Δ} {Γ} σ
   = cast-'Γ {Γ} {F0 , Δ} $ spec (⟦ Δ ⟧≈- (sym≈ unit⊸)) $ cast-Γ {Γ} {Δ} σ

⟦P⊗T⟧ : ∀ {p M N Δ} {Γ : Seq p} →
    Strat p ⟦ Γ ,,₀ M , N , Δ ⟧' → Strat p ⟦ Γ ,,₀ M ⊗ N , Δ ⟧'
⟦P⊗T⟧ { - } {M} {N} {Δ} {Γ} σ
   = cast-'Γ {Γ} $ spec (⟦ Δ ⟧≈- pasc⊘) $ cast-Γ {Γ} σ
⟦P⊗T⟧ { + } {M} {N} {Δ} {Γ} σ
   = cast+'Γ {Γ} $ spec (⟦ Δ ⟧≈+ pasc⊸) $ spec (⟦ Δ ⟧≈+ psym⊸) $ cast+Γ {Γ} σ

⟦P⅋T⟧ : ∀ {p P Q Δ} {Γ : Seq p} →
    Strat p ⟦ Γ ,,₀ P , Q , Δ ⟧' → Strat p ⟦ Γ ,,₀ P ⅋ Q , Δ ⟧'
⟦P⅋T⟧ { + } {_} {_} {Δ} {Γ} σ
    = cast+'Γ {Γ} $ spec (⟦ Δ ⟧≈+ pasc⊘) $ cast+Γ {Γ} σ
⟦P⅋T⟧ { - } {_} {_} {Δ} {Γ} σ
    = cast-'Γ {Γ} $ spec (⟦ Δ ⟧≈- pasc⊸) $ spec (⟦ Δ ⟧≈- psym⊸) $ cast-Γ {Γ} σ

⟦Psym⟧ : ∀ {p q Δ} {Γ : Seq p} {A B : Fml q} →
          Strat p ⟦ Γ ,,₀ A , B , Δ ⟧' → Strat p ⟦ Γ ,,₀ B , A , Δ ⟧'
⟦Psym⟧ { - } { - } {Δ} {Γ} {M} {N} σ
    = cast-'Γ {Γ} $ spec (⟦ Δ ⟧≈- psym⊘) $ cast-Γ {Γ} σ
⟦Psym⟧ { - } { + } {Δ} {Γ} {M} {N} σ
    = cast-'Γ {Γ} $ spec (⟦ Δ ⟧≈- psym⊸) $ cast-Γ {Γ} σ
⟦Psym⟧ { + } { + } {Δ} {Γ} {M} {N} σ
    = cast+'Γ {Γ} $ spec (⟦ Δ ⟧≈+ psym⊘) $ cast+Γ {Γ} σ
⟦Psym⟧ { + } { - } {Δ} {Γ} {M} {N} σ
    = cast+'Γ {Γ} $ spec (⟦ Δ ⟧≈+ psym⊸) $ cast+Γ {Γ} σ

⟦Pstr⟧ : ∀ {p Δ}{Γ : Seq p}{P : Fml + } →
       Strat p ⟦ Γ ,,₀ Δ ⟧' → Strat p ⟦ Γ ,,₀ P , Δ ⟧'
⟦Pstr⟧ { + } {Δ} {Γ} σ
    = cast+'Γ {Γ} $ specP (⟦ Δ ⟧≲+ ≲⊘af) $ cast+Γ {Γ} σ
⟦Pstr⟧ { - } {Δ} {Γ} σ
    = cast-'Γ {Γ} $ specN (⟦ Δ ⟧≲- ≲⊸af) $ cast-Γ {Γ} σ

⟦Pwk⟧ : ∀ {p Δ}{Γ : Seq p}{M : Fml - } →
       Strat p ⟦ Γ ,,₀ M , Δ ⟧' → Strat p ⟦ Γ ,,₀ Δ ⟧'
⟦Pwk⟧ { + } {Δ} {Γ} σ
   = cast+'Γ {Γ} $ specP (⟦ Δ ⟧≲+ ≲⊸af) $ cast+Γ {Γ} σ
⟦Pwk⟧ { - } {Δ} {Γ} σ
   = cast-'Γ {Γ} $ specN (⟦ Δ ⟧≲- ≲⊘af) $ cast-Γ {Γ} σ

⟦P⊕T₁⟧ : ∀ {p P Q Δ} {Γ : Seq p} →
       Strat p ⟦ Γ ,,₀ P , Δ ⟧' → Strat p ⟦ Γ ,,₀ P ⊕ Q , Δ ⟧'
⟦P⊕T₁⟧ { + } {_} {_} {Δ} {Γ} σ
     = cast+'Γ {Γ} $ specP (⟦ Δ ⟧≲+ (⟦ Γ ⟧' ⊘≲ ≲π₁)) $ cast+Γ {Γ} σ
⟦P⊕T₁⟧ { - } {_} {_} {Δ} {Γ} σ 
     = cast-'Γ {Γ} $ specN (⟦ Δ ⟧≲- (≲π₁ ≲⊸ ⟦ Γ ⟧')) $ cast-Γ {Γ} σ

⟦⊥'⟧ : ∀ {p} (A : Fml p) → ⟦ A ⊥' ⟧ ≡ ⟦ A ⟧
⟦⊥'⟧           F0 = refl
⟦⊥'⟧           F1 = refl
⟦⊥'⟧        (↑ P) = cong  (λ X → X ⊸o)(⟦⊥'⟧ P)
⟦⊥'⟧        (↓ M) = cong  (λ X → X ⊸o)(⟦⊥'⟧ M)
⟦⊥'⟧      (M ⊗ N) = cong₂ (λ X Y → X ⊗' Y) (⟦⊥'⟧ M) (⟦⊥'⟧ N)
⟦⊥'⟧      (P ⅋ Q) = cong₂ (λ X Y → X ⊗' Y) (⟦⊥'⟧ P) (⟦⊥'⟧ Q)
⟦⊥'⟧      (P ⊕ Q) = cong₂ (λ X Y → X ×' Y) (⟦⊥'⟧ P) (⟦⊥'⟧ Q)
⟦⊥'⟧      (M & N) = cong₂ (λ X Y → X ×' Y) (⟦⊥'⟧ M) (⟦⊥'⟧ N)
⟦⊥'⟧ { + }(A ⊘ M) = cong₂ (λ X Y → Y ⊸ X) (⟦⊥'⟧ A) (⟦⊥'⟧ M)
⟦⊥'⟧ { - }(A ⊘ M) = cong₂ (λ X Y → X ⊘' Y) (⟦⊥'⟧ A) (⟦⊥'⟧ M)
⟦⊥'⟧ { + }(A ◁ P) = cong₂ (λ X Y → X ⊘' Y) (⟦⊥'⟧ A) (⟦⊥'⟧ P)
⟦⊥'⟧ { - }(A ◁ P) = cong₂ (λ X Y → Y ⊸ X) (⟦⊥'⟧ A) (⟦⊥'⟧ P)

⟦Pid⟧ : ∀ {M : Fml - } → Strat - ⟦ M , M ⊥' , ε ⟧'
⟦Pid⟧ {M} with ⟦ M ⊥' ⟧ | ⟦⊥'⟧ M 
...          | .(⟦ M ⟧) | refl = idσ --⟦ M ⟧

⅋⅋ : ∀ {Δ} → ispol + Δ → Fml +
⅋⅋ ε = F0
⅋⅋ (P , Γ) = P ⅋ (⅋⅋ Γ)

⅋⅋lemma : ∀ {p}(Γ : Seq p){Δ}(Δ' : ispol + Δ)
   → ⟦ Γ ,,₀ Δ ⟧' ≈ ⟦ Γ ,,₂ ⅋⅋ Δ' ⟧'

⅋⅋lemma { - } Γ {ε} ε
 with ⟦ Γ ,,₀ ε ⟧' | ⟦,Δ⟧is⟦Δ⟧- Γ ε | (Γ ,,₂ ⅋⅋ ε) F | ,,F◁ Γ (⅋⅋ ε)
... | .(⟦ ε ⟧- ⟦ Γ ⟧') | refl | .(Γ F ◁ ⅋⅋ ε) | refl = sym≈ unit⊸

⅋⅋lemma { + } Γ {ε} ε with
  ⟦ Γ ,,₀ ε ⟧' | ⟦,Δ⟧is⟦Δ⟧+ Γ ε | (Γ ,,₂ ⅋⅋ ε) F | ,,F◁ Γ (⅋⅋ ε)
... | .(⟦ ε ⟧+ ⟦ Γ ⟧') | refl | .(Γ F ◁ ⅋⅋ ε) | refl = sym≈ unit⊘

⅋⅋lemma { - } Γ {.P , Δ} (P , Δ')
 with (Γ ,,₀ (P , Δ)) | ,,₂₀ Γ P Δ |
      (Γ ,,₂ ⅋⅋ (P , Δ')) F | ,,F◁ Γ (⅋⅋ (P , Δ'))
... | .(Γ ,,₂ P ,,₀ Δ) | refl | .(Γ F ◁ ⅋⅋ (P , Δ')) | refl
   = σ ∘≈ τ t
 where σ = ⅋⅋lemma (Γ ,,₂ P) Δ' 
       τ : ∀ {G} → G ≡ ⟦ ⅋⅋ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ ⟧')
           → G ≈ ⟦ P ⟧ ⊗' ⟦ ⅋⅋ Δ' ⟧ ⊸ ⟦ Γ ⟧'
       τ .{⟦ ⅋⅋ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ F ⟧)} refl = pasc⊸ ∘≈ (sym⊗ ≈⊸ _)
       t : ⟦ (Γ ,,₂ P) ,,₂ ⅋⅋ Δ' ⟧' ≡ ⟦ ⅋⅋ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ ⟧')
       t with (Γ ,,₂ P) F | ,,F◁ Γ P
              | ((Γ ,,₂ P) ,,₂ ⅋⅋ Δ') F | ,,F◁ (Γ ,,₂ P) (⅋⅋ Δ')
       t | .((Γ F) ◁ P) | refl | .(((Γ F) ◁ P) ◁ ⅋⅋ Δ') | refl = refl

⅋⅋lemma { + } Γ {.P , Δ} (P , Δ')
 with (Γ ,,₀ (P , Δ)) | ,,₂₀ Γ P Δ |
      (Γ ,,₂ ⅋⅋ (P , Δ')) F | ,,F◁ Γ (⅋⅋ (P , Δ'))
... | .(Γ ,,₂ P ,,₀ Δ) | refl | .(Γ F ◁ ⅋⅋ (P , Δ')) | refl
   = σ ∘≈ τ t
 where σ = ⅋⅋lemma (Γ ,,₂ P) Δ' 
       τ : ∀ {G} → G ≡ (⟦ Γ ⟧' ⊘' ⟦ P ⟧) ⊘' ⟦ ⅋⅋ Δ' ⟧
           → G ≈ ⟦ Γ ⟧' ⊘' (⟦ P ⟧ ⊗' ⟦ ⅋⅋ Δ' ⟧)
       τ .{(⟦ Γ F ⟧ ⊘' ⟦ P ⟧) ⊘' ⟦ ⅋⅋ Δ' ⟧} refl = pasc⊘
       t : ⟦ (Γ ,,₂ P) ,,₂ ⅋⅋ Δ' ⟧' ≡ (⟦ Γ ⟧' ⊘' ⟦ P ⟧) ⊘' ⟦ ⅋⅋ Δ' ⟧
       t with (Γ ,,₂ P) F | ,,F◁ Γ P
              | ((Γ ,,₂ P) ,,₂ ⅋⅋ Δ') F | ,,F◁ (Γ ,,₂ P) (⅋⅋ Δ')
       t | .((Γ F) ◁ P) | refl | .(((Γ F) ◁ P) ◁ ⅋⅋ Δ') | refl = refl

⊗⊗lemma : ∀ {p}(Γ : Seq p){Δ}(Δ' : ispol - Δ)
   → ⟦ Γ ,,₀ Δ ⟧' ≈ ⟦ Γ ,,₂ ⊗⊗ Δ' ⟧'

⊗⊗lemma { + } Γ {ε} ε
 with ⟦ Γ ,,₀ ε ⟧' | ⟦,Δ⟧is⟦Δ⟧+ Γ ε | (Γ ,,₂ ⊗⊗ ε) F | ,,F⊘ Γ (⊗⊗ ε)
... | .(⟦ ε ⟧- ⟦ Γ ⟧') | refl | .(Γ F ⊘ ⊗⊗ ε) | refl = sym≈ unit⊸

⊗⊗lemma { - } Γ {ε} ε with
  ⟦ Γ ,,₀ ε ⟧' | ⟦,Δ⟧is⟦Δ⟧- Γ ε | (Γ ,,₂ ⊗⊗ ε) F | ,,F⊘ Γ (⊗⊗ ε)
... | .(⟦ ε ⟧+ ⟦ Γ ⟧') | refl | .(Γ F ⊘ ⊗⊗ ε) | refl = sym≈ unit⊘

⊗⊗lemma { + } Γ {.P , Δ} (P , Δ')
 with (Γ ,,₀ (P , Δ)) | ,,₂₀ Γ P Δ |
      (Γ ,,₂ ⊗⊗ (P , Δ')) F | ,,F⊘ Γ (⊗⊗ (P , Δ'))
... | .(Γ ,,₂ P ,,₀ Δ) | refl | .(Γ F ⊘ ⊗⊗ (P , Δ')) | refl
   = σ ∘≈ τ t
 where σ = ⊗⊗lemma (Γ ,,₂ P) Δ' 
       τ : ∀ {G} → G ≡ ⟦ ⊗⊗ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ ⟧')
           → G ≈ ⟦ P ⟧ ⊗' ⟦ ⊗⊗ Δ' ⟧ ⊸ ⟦ Γ ⟧'
       τ .{⟦ ⊗⊗ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ F ⟧)} refl = pasc⊸ ∘≈ (sym⊗ ≈⊸ _)
       t : ⟦ (Γ ,,₂ P) ,,₂ ⊗⊗ Δ' ⟧' ≡ ⟦ ⊗⊗ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ ⟧')
       t with (Γ ,,₂ P) F | ,,F⊘ Γ P
              | ((Γ ,,₂ P) ,,₂ ⊗⊗ Δ') F | ,,F⊘ (Γ ,,₂ P) (⊗⊗ Δ')
       t | .((Γ F) ⊘ P) | refl | .(((Γ F) ⊘ P) ⊘ ⊗⊗ Δ') | refl = refl

⊗⊗lemma { - } Γ {.P , Δ} (P , Δ')
 with (Γ ,,₀ (P , Δ)) | ,,₂₀ Γ P Δ |
      (Γ ,,₂ ⊗⊗ (P , Δ')) F | ,,F⊘ Γ (⊗⊗ (P , Δ'))
... | .(Γ ,,₂ P ,,₀ Δ) | refl | .(Γ F ⊘ ⊗⊗ (P , Δ')) | refl
   = σ ∘≈ τ t
 where σ = ⊗⊗lemma (Γ ,,₂ P) Δ' 
       τ : ∀ {G} → G ≡ (⟦ Γ ⟧' ⊘' ⟦ P ⟧) ⊘' ⟦ ⊗⊗ Δ' ⟧
           → G ≈ ⟦ Γ ⟧' ⊘' (⟦ P ⟧ ⊗' ⟦ ⊗⊗ Δ' ⟧)
       τ .{(⟦ Γ F ⟧ ⊘' ⟦ P ⟧) ⊘' ⟦ ⊗⊗ Δ' ⟧} refl = pasc⊘
       t : ⟦ (Γ ,,₂ P) ,,₂ ⊗⊗ Δ' ⟧' ≡ (⟦ Γ ⟧' ⊘' ⟦ P ⟧) ⊘' ⟦ ⊗⊗ Δ' ⟧
       t with (Γ ,,₂ P) F | ,,F⊘ Γ P
              | ((Γ ,,₂ P) ,,₂ ⊗⊗ Δ') F | ,,F⊘ (Γ ,,₂ P) (⊗⊗ Δ')
       t | .((Γ F) ⊘ P) | refl | .(((Γ F) ⊘ P) ⊘ ⊗⊗ Δ') | refl = refl
