module WS-Sem-Fsc where
-- in which we give semantics to WS formulas, sequents and contexts

open import Function
open import Relation.Binary.PropositionalEquality

open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import WS-Syn

-- Semantics of Formulas and Sequents of WS

⟦_⟧ : {p : Pol} → Fml p → Game
⟦   F1  ⟧         = I
⟦   F⊥  ⟧         = o
⟦   F0  ⟧         = I
⟦   F⊤  ⟧         = o
⟦ M ⊗ N ⟧         = ⟦ M ⟧ ⊗' ⟦ N ⟧
⟦ P ⅋ Q ⟧         = ⟦ P ⟧ ⊗' ⟦ Q ⟧
⟦ M & N ⟧         = ⟦ M ⟧ ×' ⟦ N ⟧
⟦ P ⊕ Q ⟧         = ⟦ P ⟧ ×' ⟦ Q ⟧
⟦ _⊘_ { - } M N ⟧ = ⟦ M ⟧ ⊘' ⟦ N ⟧ 
⟦ _⊘_ { + } P N ⟧ = ⟦ N ⟧ ⊸ ⟦ P ⟧
⟦ _◁_ { + } P Q ⟧ = ⟦ P ⟧ ⊘' ⟦ Q ⟧ 
⟦ _◁_ { - } M P ⟧ = ⟦ P ⟧ ⊸ ⟦ M ⟧
⟦ ω⊕ P ⟧          = ω× ⟦ P ⟧
⟦ ω& N ⟧          = ω× ⟦ N ⟧

infixr 8 _F
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

⟦_⟧σ- : ∀ {M N} Γ → Strat - (M ⊸̂ N) → Strat - (⟦ Γ ⟧- M ⊸̂ ⟦ Γ ⟧- N)
⟦ ε ⟧σ-             σ = σ
⟦ _,_ { - } M Γ ⟧σ- σ = ⟦ Γ ⟧σ- (σ ⊘s idσ)
⟦ _,_ { + } P Γ ⟧σ- σ = ⟦ Γ ⟧σ- (idσ ⊸ŝ σ)

⟦_⟧σ+ : ∀ {M N} Γ → Strat - (M ⊸̂ N) → Strat - (⟦ Γ ⟧+ M ⊸̂ ⟦ Γ ⟧+ N)
⟦ ε ⟧σ+             σ = σ
⟦ _,_ { + } P Γ ⟧σ+ σ = ⟦ Γ ⟧σ+ (σ ⊘s idσ)
⟦ _,_ { - } M Γ ⟧σ+ σ = ⟦ Γ ⟧σ+ (idσ ⊸ŝ σ)

-- Lemmas about Semantics and Contexts

⟦Δ⟧-⟦M⟧≡⟦M,Δ⟧ : ∀ {M : Fml - } Γ → ⟦ Γ ⟧- ⟦ M ⟧ ≡ ⟦ M , Γ ⟧'
⟦Δ⟧-⟦M⟧≡⟦M,Δ⟧ ε               = refl
⟦Δ⟧-⟦M⟧≡⟦M,Δ⟧ (_,_ { - } _ Γ) = ⟦Δ⟧-⟦M⟧≡⟦M,Δ⟧ Γ
⟦Δ⟧-⟦M⟧≡⟦M,Δ⟧ (_,_ { + } _ Γ) = ⟦Δ⟧-⟦M⟧≡⟦M,Δ⟧ Γ

⟦Δ⟧+⟦P⟧≡⟦P,Δ⟧ : ∀ {P : Fml +} Γ → ⟦ Γ ⟧+ ⟦ P ⟧ ≡ ⟦ P , Γ ⟧'
⟦Δ⟧+⟦P⟧≡⟦P,Δ⟧ ε               = refl
⟦Δ⟧+⟦P⟧≡⟦P,Δ⟧ (_,_ { - } _ Γ) = ⟦Δ⟧+⟦P⟧≡⟦P,Δ⟧ Γ
⟦Δ⟧+⟦P⟧≡⟦P,Δ⟧ (_,_ { + } _ Γ) = ⟦Δ⟧+⟦P⟧≡⟦P,Δ⟧ Γ

,,F⊘ : ∀ {p} (Γ : Seq p ) M → (Γ F) ⊘ M ≡ (Γ ,,₀ [ M ]) F
,,F⊘ (M , ε) N = refl
,,F⊘ (M , (_,_ { - } O Γ)) N = ,,F⊘ (M ⊘ O , Γ) N
,,F⊘ (M , (_,_ { + } P Γ)) N = ,,F⊘ (M ◁ P , Γ) N

,,F◁ : ∀ {p} (Γ : Seq p ) M → (Γ F) ◁ M ≡ (Γ ,,₀ [ M ]) F
,,F◁ (M , ε) N = refl
,,F◁ (M , (_,_ { - } O Γ)) N = ,,F◁ (M ⊘ O , Γ) N
,,F◁ (M , (_,_ { + } P Γ)) N = ,,F◁ (M ◁ P , Γ) N

,,₀assoc' : ∀ {p q}(Γ : Seq p)(Δ : Fml q) Ε → Γ ,,₀ ([ Δ ] ,, Ε) ≡ (Γ ,,₀ [ Δ ]) ,,₀ Ε
,,₀assoc' Γ A B = sym $ ,,₀assoc Γ {[ A ]} {B}

,,₀F : ∀ {p}(Γ : Seq p) Δ → (Γ F , Δ) F ≡ (Γ ,,₀ Δ) F 
,,₀F { - } Γ ε = cong _F (sym $ ,,₀ε Γ)
,,₀F { - } Γ (_,_ { - } M Δ) rewrite ,,₀assoc' Γ M Δ | ,,F⊘ Γ M = ,,₀F (Γ ,,₀ (M , ε)) Δ
,,₀F { - } Γ (_,_ { + } P Δ) rewrite ,,₀assoc' Γ P Δ | ,,F◁ Γ P = ,,₀F (Γ ,,₀ (P , ε)) Δ
,,₀F { + } Γ ε = cong _F (sym $ ,,₀ε Γ)
,,₀F { + } Γ (_,_ { - } M Δ) rewrite ,,₀assoc' Γ M Δ | ,,F⊘ Γ M = ,,₀F (Γ ,,₀ (M , ε)) Δ
,,₀F { + } Γ (_,_ { + } P Δ) rewrite ,,₀assoc' Γ P Δ | ,,F◁ Γ P = ,,₀F (Γ ,,₀ (P , ε)) Δ

⟦Δ⟧+≡⟦,Δ⟧ : ∀ (Γ : Seq +) Δ → ⟦ Δ ⟧+ ⟦ Γ ⟧' ≡ ⟦ Γ ,,₀ Δ ⟧'
⟦Δ⟧+≡⟦,Δ⟧ Γ Δ rewrite cong ⟦_⟧ (sym $ ,,₀F Γ Δ) = ⟦Δ⟧+⟦P⟧≡⟦P,Δ⟧ {Γ F} Δ

-- with ⟦ Γ ,,₀ Δ ⟧'

⟦Δ⟧-≡⟦,Δ⟧ : ∀ (Γ : Seq -) Δ → ⟦ Δ ⟧- ⟦ Γ ⟧' ≡ ⟦ Γ ,,₀ Δ ⟧'
⟦Δ⟧-≡⟦,Δ⟧ Γ Δ rewrite cong ⟦_⟧ (sym $ ,,₀F Γ Δ) = ⟦Δ⟧-⟦M⟧≡⟦M,Δ⟧ {Γ F} Δ

⟦,Δ⟧≡⟦Δ⟧+ : ∀ (Γ : Seq +) Δ → ⟦ Γ ,,₀ Δ ⟧' ≡ ⟦ Δ ⟧+ ⟦ Γ ⟧'
⟦,Δ⟧≡⟦Δ⟧+ Γ Δ = sym $ ⟦Δ⟧+≡⟦,Δ⟧ Γ Δ

⟦,Δ⟧≡⟦Δ⟧- : ∀ (Γ : Seq -) Δ → ⟦ Γ ,,₀ Δ ⟧' ≡ ⟦ Δ ⟧- ⟦ Γ ⟧'
⟦,Δ⟧≡⟦Δ⟧- Γ Δ = sym $ ⟦Δ⟧-≡⟦,Δ⟧ Γ Δ

-- Context distributivity isomorphisms

Γ-I≈I : ∀ Γ → ⟦ Γ ⟧- I ≈ I
Γ-I≈I ε               = id≈
Γ-I≈I (_,_ { - } _ Γ) = (⟦ Γ ⟧≈- dist01) ≈∘≈ (Γ-I≈I Γ)
Γ-I≈I (_,_ { + } _ Γ) = (⟦ Γ ⟧≈- dist02) ≈∘≈ (Γ-I≈I Γ)

distΓ- : ∀ Γ {M N} →  ⟦ Γ ⟧- (M ×' N) ≈ ⟦ Γ ⟧- M ×' ⟦ Γ ⟧- N
distΓ- ε               = id≈
distΓ- (_,_ { - } _ Γ) = (⟦ Γ ⟧≈- dist1) ≈∘≈ (distΓ- Γ)
distΓ- (_,_ { + } _ Γ) = (⟦ Γ ⟧≈- dist2) ≈∘≈ (distΓ- Γ)

distΓ+ : ∀ Γ {M N} →  ⟦ Γ ⟧+ (M ×' N) ≈ ⟦ Γ ⟧+ M ×' ⟦ Γ ⟧+ N
distΓ+ ε               = id≈
distΓ+ (_,_ { + } _ Γ) = (⟦ Γ ⟧≈+ dist1) ≈∘≈ distΓ+ Γ
distΓ+ (_,_ { - } _ Γ) = (⟦ Γ ⟧≈+ dist2) ≈∘≈ distΓ+ Γ

distΓ-ω : ∀ Γ {M} →  ⟦ Γ ⟧- (ω× M) ≈ ω× (⟦ Γ ⟧- M)
distΓ-ω ε               = id≈
distΓ-ω (_,_ { - } _ Γ) = (⟦ Γ ⟧≈- dist1ω) ≈∘≈ (distΓ-ω Γ)
distΓ-ω (_,_ { + } _ Γ) = (⟦ Γ ⟧≈- dist2ω) ≈∘≈ (distΓ-ω Γ)

distΓ+ω : ∀ Γ {P} →  ⟦ Γ ⟧+ (ω× P) ≈ ω× (⟦ Γ ⟧+ P)
distΓ+ω ε               = id≈
distΓ+ω (_,_ { + } _ Γ) = (⟦ Γ ⟧≈+ dist1ω) ≈∘≈ (distΓ+ω Γ)
distΓ+ω (_,_ { - } _ Γ) = (⟦ Γ ⟧≈+ dist2ω) ≈∘≈ (distΓ+ω Γ)

-- Useful strategy casting operations (obsolete)

cast+ : ∀ {Γ : Seq +} {Δ} → Strat + ⟦ Γ ,,₀ Δ ⟧' → Strat + (⟦ Δ ⟧+ ⟦ Γ ⟧')
cast+ {Γ} {Δ} σ = subst (Strat +) (sym $ ⟦Δ⟧+≡⟦,Δ⟧ Γ Δ) σ

cast+' : ∀ {Γ : Seq +} {Δ} → Strat + (⟦ Δ ⟧+ ⟦ Γ ⟧') → Strat + ⟦ Γ ,,₀ Δ ⟧'
cast+' {Γ} {Δ} σ = subst (Strat +) (⟦Δ⟧+≡⟦,Δ⟧ Γ Δ) σ

cast- : ∀ {Γ : Seq - } {Δ} → Strat - ⟦ Γ ,,₀ Δ ⟧' → Strat - (⟦ Δ ⟧- ⟦ Γ ⟧')
cast- {Γ} {Δ} σ = subst (Strat -) (sym $ ⟦Δ⟧-≡⟦,Δ⟧ Γ Δ) σ

cast-' : ∀ {Γ : Seq - } {Δ} → Strat - (⟦ Δ ⟧- ⟦ Γ ⟧') → Strat - ⟦ Γ ,,₀ Δ ⟧'
cast-' {Γ} {Δ} σ = subst (Strat -) (⟦Δ⟧-≡⟦,Δ⟧ Γ Δ) σ

