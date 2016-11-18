module WS-Sem-Tails where
-- in which we give semantics to some non-core proof rules of WS

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_+_ to _+'_)

open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import WS-Syn
open import WS-Sem-Fsc

⟦P1T⟧ : ∀ {p Δ}{Γ : Seq p} → Strat p ⟦ Γ ,,₀ Δ ⟧' → Strat p ⟦ Γ ,,₀ F1 , Δ ⟧'
⟦P1T⟧ { + } {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (F1 , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ Δ = σ ∘≈ ⟦ Δ ⟧≈+ (unit⊸ ^-1)
⟦P1T⟧ { - } {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (F1 , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ Δ = ⟦ Δ ⟧≈- (unit⊘ ^-1) ≈∘ σ

⟦P1Tb⟧ : ∀ {p Δ}{Γ : Seq p} → Strat p ⟦ Γ ,,₀ F1 , Δ ⟧' → Strat p ⟦ Γ ,,₀ Δ ⟧'
⟦P1Tb⟧ { + } {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (F1 , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ Δ = σ ∘≈ ⟦ Δ ⟧≈+ unit⊸
⟦P1Tb⟧ { - } {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (F1 , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ Δ = ⟦ Δ ⟧≈- unit⊘ ≈∘ σ

⟦P0T⟧ : ∀ {p Δ}{Γ : Seq p} → Strat p ⟦ Γ ,,₀ Δ ⟧' → Strat p ⟦ Γ ,,₀ F0 , Δ ⟧'
⟦P0T⟧ { + } {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (F0 , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ Δ = σ ∘≈ ⟦ Δ ⟧≈+ (unit⊘ ^-1)
⟦P0T⟧ { - } {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (F0 , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ Δ = ⟦ Δ ⟧≈- (unit⊸ ^-1) ≈∘ σ

⟦P0Tb⟧ : ∀ {p Δ}{Γ : Seq p} → Strat p ⟦ Γ ,,₀ F0 , Δ ⟧' → Strat p ⟦ Γ ,,₀ Δ ⟧'
⟦P0Tb⟧ { + } {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (F0 , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ Δ = σ ∘≈ ⟦ Δ ⟧≈+ unit⊘
⟦P0Tb⟧ { - } {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (F0 , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ Δ = ⟦ Δ ⟧≈- unit⊸ ≈∘ σ

⟦P⊗T⟧ : ∀ {p M N Δ} {Γ : Seq p} → Strat p ⟦ Γ ,,₀ M , N , Δ ⟧' → Strat p ⟦ Γ ,,₀ M ⊗ N , Δ ⟧'
⟦P⊗T⟧ { - } {M} {N} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (M , N , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ (M ⊗ N , Δ) = ⟦ Δ ⟧≈- pasc⊘ ≈∘ σ
⟦P⊗T⟧ { + } {M} {N} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (M , N , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ (M ⊗ N , Δ) = σ ∘≈ ⟦ Δ ⟧≈+ psym⊸ ∘≈ ⟦ Δ ⟧≈+ pasc⊸

⟦P⊗Tb⟧ : ∀ {p M N Δ} {Γ : Seq p} → Strat p ⟦ Γ ,,₀ M ⊗ N , Δ ⟧' → Strat p ⟦ Γ ,,₀ M , N , Δ ⟧'
⟦P⊗Tb⟧ { - } {M} {N} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (M , N , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ (M ⊗ N , Δ) = ⟦ Δ ⟧≈- (pasc⊘ ^-1) ≈∘  σ
⟦P⊗Tb⟧ { + } {M} {N} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (M , N , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ (M ⊗ N , Δ)
  = σ ∘≈ ⟦ Δ ⟧≈+ (pasc⊸ ^-1) ∘≈ ⟦ Δ ⟧≈+ (psym⊸ ^-1)

⟦P⅋T⟧ : ∀ {p P Q Δ} {Γ : Seq p} → Strat p ⟦ Γ ,,₀ P , Q , Δ ⟧' → Strat p ⟦ Γ ,,₀ P ⅋ Q , Δ ⟧'
⟦P⅋T⟧ { + } {P} {Q} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (P , Q , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ (P ⅋ Q , Δ) = σ ∘≈ ⟦ Δ ⟧≈+ pasc⊘
⟦P⅋T⟧ { - } {P} {Q} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (P , Q , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ (P ⅋ Q , Δ) = ⟦ Δ ⟧≈- pasc⊸ ≈∘ ⟦ Δ ⟧≈- psym⊸ ≈∘ σ

⟦P⅋Tb⟧ : ∀ {p P Q Δ} {Γ : Seq p} → Strat p ⟦ Γ ,,₀ P ⅋ Q , Δ ⟧' → Strat p ⟦ Γ ,,₀ P , Q , Δ ⟧'
⟦P⅋Tb⟧ { + } {P} {Q} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (P , Q , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ (P ⅋ Q , Δ) = σ ∘≈ ⟦ Δ ⟧≈+ (pasc⊘ ^-1)
⟦P⅋Tb⟧ { - } {P} {Q} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (P , Q , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ (P ⅋ Q , Δ) = ⟦ Δ ⟧≈- (psym⊸ ^-1) ≈∘ ⟦ Δ ⟧≈- (pasc⊸ ^-1) ≈∘ σ

⟦Psym⟧ : ∀ {p q Δ} {Γ : Seq p} {A B : Fml q} → Strat p ⟦ Γ ,,₀ A , B , Δ ⟧' → Strat p ⟦ Γ ,,₀ B , A , Δ ⟧'
⟦Psym⟧ { - } { - } {Δ} {Γ} {M} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (M , N , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ (N , M , Δ) = ⟦ Δ ⟧≈- psym⊘ ≈∘ σ
⟦Psym⟧ { - } { + } {Δ} {Γ} {M} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (M , N , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ (N , M , Δ) = ⟦ Δ ⟧≈- psym⊸ ≈∘ σ
⟦Psym⟧ { + } { + } {Δ} {Γ} {M} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (M , N , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ (N , M , Δ) = σ ∘≈ ⟦ Δ ⟧≈+ psym⊘
⟦Psym⟧ { + } { - } {Δ} {Γ} {M} {N} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (M , N , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ (N , M , Δ) = σ ∘≈ ⟦ Δ ⟧≈+ psym⊸

⟦Pstr⟧ : ∀ {p Δ}{Γ : Seq p}{P : Fml + } → Strat p ⟦ Γ ,,₀ Δ ⟧' → Strat p ⟦ Γ ,,₀ P , Δ ⟧'
⟦Pstr⟧ { + } {Δ} {Γ} {P} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ Δ | ⟦,Δ⟧≡⟦Δ⟧+ Γ (P , Δ) = σ ∘≲ ⟦ Δ ⟧≲+ ≲⊘af
⟦Pstr⟧ { - } {Δ} {Γ} {P} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ Δ | ⟦,Δ⟧≡⟦Δ⟧- Γ (P , Δ) = ⟦ Δ ⟧≲- ≲⊸af ≲∘ σ

⟦Pwk⟧ : ∀ {p Δ}{Γ : Seq p}{M : Fml - } → Strat p ⟦ Γ ,,₀ M , Δ ⟧' → Strat p ⟦ Γ ,,₀ Δ ⟧'
⟦Pwk⟧ { + } {Δ} {Γ} {M} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ Δ | ⟦,Δ⟧≡⟦Δ⟧+ Γ (M , Δ) = σ ∘≲ (⟦ Δ ⟧≲+ ≲⊸af)
⟦Pwk⟧ { - } {Δ} {Γ} {M} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ Δ | ⟦,Δ⟧≡⟦Δ⟧- Γ (M , Δ) = ⟦ Δ ⟧≲- ≲⊘af ≲∘ σ

--⟦P⊥⟧ : ∀ {P Γ} → Strat - ⟦ ↑ P , Γ ⟧' → Strat - ⟦ ↑ F0 , P , Γ ⟧'
--⟦P⊥⟧ {P} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- [ ↑ P ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- (↑ F0 , P , ε) Γ = ⟦ Γ ⟧≈- ↑≈⊸o ≈∘ σ

--⟦P⊥b⟧ : ∀ {P Γ} → Strat - ⟦ ↑ F0 , P , Γ ⟧' → Strat - ⟦ ↑ P , Γ ⟧'
--⟦P⊥b⟧ {P} {Γ} σ  rewrite ⟦,Δ⟧≡⟦Δ⟧- [ ↑ P ]' Γ | ⟦,Δ⟧≡⟦Δ⟧- (↑ F0 , P , ε) Γ = ⟦ Γ ⟧≈- (↑≈⊸o ^-1) ≈∘ σ

--⟦P⊤⟧ : ∀ {M Γ} → Strat + ⟦ ↓ M , Γ ⟧' → Strat + ⟦ ↓ F1 , M , Γ ⟧'
--⟦P⊤⟧ {M} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ [ ↓ M ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ (↓ F1 , M , ε) Γ = σ ∘≈ ⟦ Γ ⟧≈+ ↑≈⊸o

--⟦P⊤b⟧ : ∀ {M Γ} → Strat + ⟦ ↓ F1 , M , Γ ⟧' → Strat + ⟦ ↓ M , Γ ⟧'
--⟦P⊤b⟧ {M} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ [ ↓ M ]' Γ | ⟦,Δ⟧≡⟦Δ⟧+ (↓ F1 , M , ε) Γ = σ ∘≈ ⟦ Γ ⟧≈+ (↑≈⊸o ^-1)

⟦P⊕T₁⟧ : ∀ {p P Q Δ} {Γ : Seq p} → Strat p ⟦ Γ ,,₀ P , Δ ⟧' → Strat p ⟦ Γ ,,₀ P ⊕ Q , Δ ⟧'
⟦P⊕T₁⟧ { + } {P} {Q} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (P , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ (P ⊕ Q , Δ) = σ ∘≲ ⟦ Δ ⟧≲+ (⟦ Γ ⟧' ⊘≲ ≲π₁)
⟦P⊕T₁⟧ { - } {P} {Q} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (P , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ (P ⊕ Q , Δ) = ⟦ Δ ⟧≲- (≲π₁ ≲⊸ ⟦ Γ ⟧') ≲∘ σ

⟦P⊕T₂⟧ : ∀ {p P Q Δ} {Γ : Seq p} → Strat p ⟦ Γ ,,₀ Q , Δ ⟧' → Strat p ⟦ Γ ,,₀ P ⊕ Q , Δ ⟧'
⟦P⊕T₂⟧ { + } {P} {Q} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (Q , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ (P ⊕ Q , Δ) = σ ∘≲ ⟦ Δ ⟧≲+ (⟦ Γ ⟧' ⊘≲ ≲π₂)
⟦P⊕T₂⟧ { - } {P} {Q} {Δ} {Γ} σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (Q , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ (P ⊕ Q , Δ) = ⟦ Δ ⟧≲- (≲π₂ ≲⊸ ⟦ Γ ⟧') ≲∘ σ

⟦P⊕Tω⟧ : ∀ {p P Δ} {Γ : Seq p} → ℕ → Strat p ⟦ Γ ,,₀ P , Δ ⟧' → Strat p ⟦ Γ ,,₀ ω⊕ P , Δ ⟧'
⟦P⊕Tω⟧ { + } {P} {Δ} {Γ} n σ rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ (P , Δ) | ⟦,Δ⟧≡⟦Δ⟧+ Γ ( ω⊕ P , Δ) = σ ∘≲ ⟦ Δ ⟧≲+ (⟦ Γ ⟧' ⊘≲ ≲π n)
⟦P⊕Tω⟧ { - } {P} {Δ} {Γ} n σ rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ (P , Δ) | ⟦,Δ⟧≡⟦Δ⟧- Γ ( ω⊕ P , Δ) = ⟦ Δ ⟧≲- (≲π n ≲⊸ ⟦ Γ ⟧') ≲∘ σ
