module WS-Sem-Core where
-- in which we give semantics to the core rules of WS

open import Function
open import Relation.Binary.PropositionalEquality

open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import WS-Syn
open import WS-Sem-Fsc
open import Data.Nat renaming (_+_ to _+'_)

-- Semantics of Core Proofs

⟦P1⟧ : ∀ {Γ} → Strat - ⟦ F1 , Γ ⟧'
⟦P1⟧ {Γ} rewrite ⟦,Δ⟧≡⟦Δ⟧- [ F1 ]' Γ = Γ-I≈I Γ ^-1 ≈∘ σI

⟦P&⟧ : ∀ {Γ M N} →
      Strat - ⟦ M , Γ ⟧' → Strat - ⟦ N , Γ ⟧' → Strat - ⟦ M & N , Γ ⟧'
⟦P&⟧ {Γ} {M} {N} σ τ rewrite ⟦,Δ⟧≡⟦Δ⟧- [ M & N ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- [ M ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- [ N ]' Γ
   = distΓ- Γ ^-1 ≈∘ (σ σ& τ)

⟦P&ω⟧ : ∀ {Γ M} → (ℕ → Strat - ⟦ M , Γ ⟧') → Strat - ⟦ ω& M , Γ ⟧'
⟦P&ω⟧ {Γ} {M} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- [ ω& M ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- [ M ]' Γ
   = distΓ-ω Γ ^-1 ≈∘ (σω& σ)

⟦P⊗⟧ : ∀ {Γ M N} →
      Strat - ⟦ M , N , Γ ⟧' → Strat - ⟦ N , M , Γ ⟧' → Strat - ⟦ M ⊗ N , Γ ⟧'
⟦P⊗⟧ {Γ} {M} {N} σ τ rewrite ⟦,Δ⟧≡⟦Δ⟧- [ M ⊗ N ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- (M , N , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧- (N , M , ε) Γ
   = ⟦ Γ ⟧≈- (dec1 ^-1) ≈∘ distΓ- Γ ^-1 ≈∘ (σ σ& τ)

⟦P⊘⟧ : ∀ {Γ : Ctx}{p : Pol}{A : Fml p }{N : Fml - } →
      Strat p ⟦ A , N , Γ ⟧' → Strat p ⟦ A ⊘ N , Γ ⟧'
⟦P⊘⟧ σ = σ

⟦P◁⟧ : ∀ {Γ : Ctx}{p : Pol}{A : Fml p }{P : Fml + } →
      Strat p ⟦ A , P , Γ ⟧' → Strat p ⟦ A ◁ P , Γ ⟧'
⟦P◁⟧ σ = σ

⟦P⊘b⟧ : ∀ {Γ : Ctx}{p : Pol}{A : Fml p }{N : Fml - } →
       Strat p ⟦ A ⊘ N , Γ ⟧' → Strat p ⟦ A , N , Γ ⟧'
⟦P⊘b⟧ σ = σ

⟦P◁b⟧ : ∀ {Γ : Ctx}{p : Pol}{A : Fml p }{P : Fml + } →
      Strat p ⟦ A ◁ P , Γ ⟧' → Strat p ⟦ A , P , Γ ⟧'
⟦P◁b⟧ σ = σ

⟦P⊕1⟧ : ∀ {Γ P Q} → Strat + ⟦ P , Γ ⟧' → Strat + ⟦ P ⊕ Q , Γ ⟧'
⟦P⊕1⟧ {Γ} {P} {Q} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ [ P ⊕ Q ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ [ P ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ [ Q ]' Γ
  = σ⊕1 (⟦ Γ ⟧+ ⟦ Q ⟧) σ ∘≈ distΓ+ Γ ^-1

⟦P⊕2⟧ : ∀ {Γ P Q} → Strat + ⟦ Q , Γ ⟧' → Strat + ⟦ P ⊕ Q , Γ ⟧'
⟦P⊕2⟧ {Γ} {P} {Q} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ [ P ⊕ Q ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ [ P ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ [ Q ]' Γ
  = σ⊕2 (⟦ Γ ⟧+ ⟦ P ⟧) σ ∘≈ distΓ+ Γ ^-1

⟦P⊕ω⟧ : ∀ {Γ P} → ℕ → Strat + ⟦ P , Γ ⟧' → Strat + ⟦ ω⊕ P , Γ ⟧'
⟦P⊕ω⟧ {Γ} {P} n σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ [ ω⊕ P ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ [ P ]' Γ
  = σ⊕n n σ ∘≈ distΓ+ω Γ ^-1

⟦P⅋1⟧ : ∀ {Γ P Q} → Strat + ⟦ P , Q , Γ ⟧' → Strat + ⟦ P ⅋ Q , Γ ⟧'
⟦P⅋1⟧ {Γ} {P} {Q} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ [ P ⅋ Q ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ (P , Q , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧+ (Q , P , ε) Γ
  = σ⊕1 (⟦ Γ ⟧+ ⟦ Q ◁ P ⟧) σ ∘≈ distΓ+ Γ ^-1 ∘≈ ⟦ Γ ⟧≈+ (dec1 ^-1)

⟦P⅋2⟧ : ∀ {Γ P Q} → Strat + ⟦ Q , P , Γ ⟧' → Strat + ⟦ P ⅋ Q , Γ ⟧'
⟦P⅋2⟧ {Γ} {P} {Q} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ [ P ⅋ Q ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ (P , Q , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧+ (Q , P , ε) Γ
  = σ⊕2 (⟦ Γ ⟧+ ⟦ P ◁ Q ⟧) σ ∘≈ distΓ+ Γ ^-1 ∘≈ ⟦ Γ ⟧≈+ (dec1 ^-1)

⟦P⊥⊘⟧ : ∀ {Γ} {P : Fml +} {N} → Strat - ⟦ F⊥ , P ⊘ N , Γ ⟧' → Strat - ⟦ F⊥ , P , N , Γ ⟧'
⟦P⊥⊘⟧ {Γ} {P} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , P ⊘ N , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , P , N , ε) Γ = ⟦ Γ ⟧≈- lfe' ≈∘ σ

⟦P⊤◁⟧ : ∀ {Γ} {N : Fml -} {P} → Strat + ⟦ F⊤ , N ◁ P , Γ ⟧' → Strat + ⟦ F⊤ , N , P , Γ ⟧'
⟦P⊤◁⟧ {Γ} {N} {P} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , N ◁ P , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , N , P , ε) Γ = σ ∘≈ ⟦ Γ ⟧≈+ lfe'

⟦P⊥⅋⟧ : ∀ {Γ P Q} → Strat - ⟦ F⊥ , P ⅋ Q , Γ ⟧' → Strat - ⟦ F⊥ , P , Q , Γ ⟧'
⟦P⊥⅋⟧ {Γ} {P} {Q} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , P ⅋ Q , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , P , Q , ε) Γ = ⟦ Γ ⟧≈- (sym⊗ ≈⊸ o ≈∘≈ pasc⊸ ^-1) ≈∘ σ

⟦P⊤⊗⟧ : ∀ {Γ M N} → Strat + ⟦ F⊤ , M ⊗ N , Γ ⟧' → Strat + ⟦ F⊤ , M , N , Γ ⟧'
⟦P⊤⊗⟧ {Γ} {M} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , M ⊗ N , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , M , N , ε) Γ = σ ∘≈ ⟦ Γ ⟧≈+ (sym⊗ ≈⊸ o ≈∘≈ pasc⊸ ^-1)

⟦P⊥+⟧ : ∀ {P : Fml +} → Strat + ⟦ P , ε ⟧' → Strat - ⟦ F⊥ , P , ε ⟧'
⟦P⊥+⟧ σ = ↑≈⊸o ≈∘ (σ⊸o σ)

⟦P⊤-⟧ : ∀ {N : Fml -} → Strat - ⟦ N , ε ⟧' → Strat + ⟦ F⊤ , N , ε ⟧'
⟦P⊤-⟧ σ = (σ⊸o σ) ∘≈ ↑≈⊸o

⟦P⊥-⟧ : ∀ {Γ} {N : Fml -} → Strat - ⟦ F⊥ , Γ ⟧' → Strat - ⟦ F⊥ , N , Γ ⟧'
⟦P⊥-⟧ {Γ} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧- (F⊥ , N , ε) Γ = ⟦ Γ ⟧≈- (abs ^-1) ≈∘ σ

⟦P⊤+⟧ : ∀ {Γ} {P : Fml +} → Strat + ⟦ F⊤ , Γ ⟧' → Strat + ⟦ F⊤ , P , Γ ⟧'
⟦P⊤+⟧ {Γ} {P} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , ε) Γ | ⟦,Δ⟧≡⟦Δ⟧+ (F⊤ , P , ε) Γ = σ ∘≈ ⟦ Γ ⟧≈+ (abs ^-1)

⟦P⊤⟧ : Strat + ⟦ F⊤ , ε ⟧'
⟦P⊤⟧ = top