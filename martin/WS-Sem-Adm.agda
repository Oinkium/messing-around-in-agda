module WS-Sem-Adm where
-- in which we give semantics to the cut and mix rules of WS

open import Function
open import Relation.Binary.PropositionalEquality

open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import WS-Syn
open import WS-Sem-Fsc

-- We first show that semantics of formulas are independent of
-- polarity:

⟦⊥'⟧ : ∀ {p} (A : Fml p) → ⟦ A ⊥' ⟧ ≡ ⟦ A ⟧
⟦⊥'⟧           F0 = refl
⟦⊥'⟧           F1 = refl
⟦⊥'⟧           F⊥ = refl
⟦⊥'⟧           F⊤ = refl
⟦⊥'⟧      (M ⊗ N) = cong₂ _⊗'_ (⟦⊥'⟧ M) (⟦⊥'⟧ N)
⟦⊥'⟧      (P ⅋ Q) = cong₂ _⊗'_ (⟦⊥'⟧ P) (⟦⊥'⟧ Q)
⟦⊥'⟧      (P ⊕ Q) = cong₂ _×'_ (⟦⊥'⟧ P) (⟦⊥'⟧ Q)
⟦⊥'⟧      (M & N) = cong₂ _×'_ (⟦⊥'⟧ M) (⟦⊥'⟧ N)
⟦⊥'⟧ { + }(A ⊘ M) = cong₂ _⊸_ (⟦⊥'⟧ M) (⟦⊥'⟧ A)
⟦⊥'⟧ { - }(A ⊘ M) = cong₂ _⊘'_ (⟦⊥'⟧ A) (⟦⊥'⟧ M)
⟦⊥'⟧ { + }(A ◁ P) = cong₂ _⊘'_ (⟦⊥'⟧ A) (⟦⊥'⟧ P)
⟦⊥'⟧ { - }(A ◁ P) = cong₂ _⊸_ (⟦⊥'⟧ P) (⟦⊥'⟧ A)
⟦⊥'⟧       (ω& M) = cong ω× (⟦⊥'⟧ M)
⟦⊥'⟧       (ω⊕ P) = cong ω× (⟦⊥'⟧ P)

-- Semantics of the Identity Rule

⟦Pid⟧ : ∀ {M : Fml - } → Strat - ⟦ M , M ⊥' , ε ⟧'
⟦Pid⟧ {M} rewrite ⟦⊥'⟧ M = idσ

-- Combining positive formulas together

⅋⅋ : ∀ {Δ} → ctxpol + Δ → Fml +
⅋⅋ ε = F0
⅋⅋ (P , Γ) = P ⅋ (⅋⅋ Γ)

⅋⅋lemma : ∀ {p}(Γ : Seq p){Δ}(Δ' : ctxpol + Δ)
   → ⟦ Γ ,,₀ Δ ⟧' ≈ ⟦ Γ ,,₀ [ ⅋⅋ Δ' ] ⟧'
⅋⅋lemma { - } Γ {ε} ε rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ ε | sym $ ,,F◁ Γ (⅋⅋ ε) = unit⊸ ^-1
⅋⅋lemma { + } Γ {ε} ε rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ ε | sym $ ,,F◁ Γ (⅋⅋ ε) = unit⊘ ^-1
⅋⅋lemma { - } Γ {.P , Δ} (P , Δ') rewrite ,,₀assoc' Γ P Δ | sym $ ,,F◁ Γ (⅋⅋ (P , Δ')) = σ ≈∘≈ τ t
 where σ = ⅋⅋lemma (Γ ,,₀ [ P ]) Δ' 
       τ : ∀ {G} → G ≡ ⟦ ⅋⅋ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ ⟧') → G ≈ ⟦ P ⟧ ⊗' ⟦ ⅋⅋ Δ' ⟧ ⊸ ⟦ Γ ⟧'
       τ .{⟦ ⅋⅋ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ F ⟧)} refl = pasc⊸ ≈∘≈ (sym⊗ ≈⊸ _)
       t : ⟦ (Γ ,,₀ [ P ]) ,,₀ [ ⅋⅋ Δ' ] ⟧' ≡ ⟦ ⅋⅋ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ ⟧')
       t rewrite sym $ ,,F◁ (Γ ,,₀ [ P ]) (⅋⅋ Δ') | sym $ ,,F◁ Γ P = refl
⅋⅋lemma { + } Γ {.P , Δ} (P , Δ') rewrite ,,₀assoc' Γ P Δ | sym $ ,,F◁ Γ (⅋⅋ (P , Δ')) = σ ≈∘≈ τ t
 where σ = ⅋⅋lemma (Γ ,,₀ [ P ]) Δ' 
       τ : ∀ {G} → G ≡ (⟦ Γ ⟧' ⊘' ⟦ P ⟧) ⊘' ⟦ ⅋⅋ Δ' ⟧ → G ≈ ⟦ Γ ⟧' ⊘' (⟦ P ⟧ ⊗' ⟦ ⅋⅋ Δ' ⟧)
       τ .{(⟦ Γ F ⟧ ⊘' ⟦ P ⟧) ⊘' ⟦ ⅋⅋ Δ' ⟧} refl = pasc⊘
       t : ⟦ Γ ,,₀ [ P ] ,,₀ [ ⅋⅋ Δ' ] ⟧' ≡ (⟦ Γ ⟧' ⊘' ⟦ P ⟧) ⊘' ⟦ ⅋⅋ Δ' ⟧
       t rewrite sym $ ,,F◁ (Γ ,,₀ [ P ]) (⅋⅋ Δ') | sym $ ,,F◁ Γ P = refl

⅋⅋lemma₂ : ∀ {p}(Γ : Seq p){Δ}(Δ' : ctxpol + Δ)(Γ₁ : Ctx)
   → ⟦ Γ ,,₀ Δ ,,₀ Γ₁ ⟧' ≈ ⟦ Γ ,,₀ [ ⅋⅋ Δ' ] ,,₀ Γ₁ ⟧'
⅋⅋lemma₂ { - } Γ {Δ} Δ' Γ₁ rewrite ⟦,Δ⟧≡⟦Δ⟧- (Γ ,,₀ Δ) Γ₁ | ⟦,Δ⟧≡⟦Δ⟧- (Γ ,,₀ [ ⅋⅋ Δ' ]) Γ₁ = ⟦ Γ₁ ⟧≈- (⅋⅋lemma Γ Δ') 
⅋⅋lemma₂ { + } Γ {Δ} Δ' Γ₁ rewrite ⟦,Δ⟧≡⟦Δ⟧+ (Γ ,,₀ Δ) Γ₁ | ⟦,Δ⟧≡⟦Δ⟧+ (Γ ,,₀ [ ⅋⅋ Δ' ]) Γ₁ = ⟦ Γ₁ ⟧≈+ (⅋⅋lemma Γ Δ') 

-- Semantics of Cut rule

compneg : ∀ {Γ : Seq - }{Δ}{N : Fml - }(Δ₁ : ctxpol + Δ) → Strat - ⟦ N , Δ ⟧' → Strat - ((⟦ N ⟧ ⊸ ⟦ Γ ⟧') ⊸̂ (⟦ Γ ,,₀ Δ ⟧'))
compneg {Γ} {Δ} {N} Δ₁ τ = ρ ∙̂ (τ' ⊸ŝ idσs)
        where τ' = (⅋⅋lemma (N , ε) Δ₁) ≈∘ τ
              ρ : Strat - ((⟦ ⅋⅋ Δ₁ ⟧ ⊸ ⟦ Γ ⟧') ⊸̂ ⟦ Γ ,,₀ Δ ⟧')
              ρ rewrite cong ⟦_⟧ (,,F◁ Γ (⅋⅋ Δ₁)) = copycat_st (wk₂ $ ⅋⅋lemma Γ Δ₁)

comppos : ∀ {Γ : Seq + }{Δ}{N : Fml - }(Δ₁ : ctxpol + Δ) → Strat - ⟦ N , Δ ⟧'
              → Strat - ((⟦ Γ ,,₀ Δ ⟧') ⊸̂ (⟦ Γ ⟧' ⊘' ⟦ N ⟧))
comppos {Γ} {Δ} {N} Δ₁ τ = (idσs ⊘s τ') ∙̂ ρ
        where τ' = (⅋⅋lemma (N , ε) Δ₁) ≈∘ τ
              ρ : Strat - (⟦ Γ ,,₀ Δ ⟧' ⊸̂ (⟦ Γ ⟧' ⊘' ⟦ ⅋⅋ Δ₁ ⟧))
              ρ rewrite cong ⟦_⟧ (,,F◁ Γ (⅋⅋ Δ₁)) = copycat_st (wk₁ $ ⅋⅋lemma Γ Δ₁)

⟦Pcut⟧ : ∀ {p Δ Γ₁}{Γ : Seq p}{M : Fml - } → ctxpol + Δ →
       Strat p ⟦ Γ ,,₀ (M ⊥') , Γ₁ ⟧' → Strat - ⟦ M , Δ ⟧' →
          Strat p ⟦ Γ ,,₀ Δ ,,₀ Γ₁ ⟧'
⟦Pcut⟧ { - } {Δ} {Γ₁} {Γ} {M} Δp σ τ rewrite ⟦,Δ⟧≡⟦Δ⟧- (Γ ,,₀ Δ) Γ₁ | ,,₀assoc' Γ (M ⊥') Γ₁
    | ⟦,Δ⟧≡⟦Δ⟧- (Γ ,,₀ [ M ⊥' ]) Γ₁ | sym $ cong (λ X → ⟦ Γ₁ ⟧- ⟦ X ⟧) (,,F◁ Γ (M ⊥'))
    | cong (λ X → ⟦ Γ₁ ⟧- (X ⊸ ⟦ Γ ⟧')) (⟦⊥'⟧ M)
        = J (⟦ Γ₁ ⟧σ- (compneg {Γ} {Δ} {M} Δp τ)) ∙` σ
⟦Pcut⟧ { + } {Δ} {Γ₁} {Γ} {M} Δp σ τ rewrite ⟦,Δ⟧≡⟦Δ⟧+ (Γ ,,₀ Δ) Γ₁ | ,,₀assoc' Γ (M ⊥') Γ₁
    | ⟦,Δ⟧≡⟦Δ⟧+ (Γ ,,₀ [ M ⊥' ]) Γ₁ | sym $ cong (λ X → ⟦ Γ₁ ⟧+ ⟦ X ⟧) (,,F◁ Γ (M ⊥'))
    | cong (λ X → ⟦ Γ₁ ⟧+ (⟦ Γ ⟧' ⊘' X)) (⟦⊥'⟧ M)
        =  σ `∙ J (⟦ Γ₁ ⟧σ+ (comppos {Γ} {Δ} {M} Δp τ)) --

-- Combining negative formulas together

⊗⊗lemma : ∀ {p}(Γ : Seq p){Δ}(Δ' : ctxpol - Δ) → ⟦ Γ ,,₀ Δ ⟧' ≈ ⟦ Γ ,,₀ [ ⊗⊗ Δ' ] ⟧'
⊗⊗lemma { + } Γ {ε} ε rewrite ⟦,Δ⟧≡⟦Δ⟧+ Γ ε | sym $ ,,F⊘ Γ (⊗⊗ ε) = unit⊸ ^-1
⊗⊗lemma { - } Γ {ε} ε rewrite ⟦,Δ⟧≡⟦Δ⟧- Γ ε | sym $ ,,F⊘ Γ (⊗⊗ ε) = unit⊘ ^-1
⊗⊗lemma { + } Γ {.P , Δ} (P , Δ') rewrite ,,₀assoc' Γ P Δ | sym $ ,,F⊘ Γ (⊗⊗ (P , Δ')) = σ ≈∘≈ τ t
 where σ = ⊗⊗lemma (Γ ,,₀ [ P ]) Δ' 
       τ : ∀ {G} → G ≡ ⟦ ⊗⊗ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ ⟧') → G ≈ ⟦ P ⟧ ⊗' ⟦ ⊗⊗ Δ' ⟧ ⊸ ⟦ Γ ⟧'
       τ .{⟦ ⊗⊗ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ F ⟧)} refl = pasc⊸ ≈∘≈ (sym⊗ ≈⊸ _)
       t : ⟦ (Γ ,,₀ [ P ]) ,,₀ [ ⊗⊗ Δ' ] ⟧' ≡ ⟦ ⊗⊗ Δ' ⟧ ⊸ (⟦ P ⟧ ⊸ ⟦ Γ ⟧')
       t rewrite sym $ ,,F⊘ (Γ ,,₀ [ P ]) (⊗⊗ Δ') | sym $ ,,F⊘ Γ P = refl
⊗⊗lemma { - } Γ {.P , Δ} (P , Δ') rewrite ,,₀assoc' Γ P Δ | sym $ ,,F⊘ Γ (⊗⊗ (P , Δ')) = σ ≈∘≈ τ t
 where σ = ⊗⊗lemma (Γ ,,₀ [ P ]) Δ' 
       τ : ∀ {G} → G ≡ (⟦ Γ ⟧' ⊘' ⟦ P ⟧) ⊘' ⟦ ⊗⊗ Δ' ⟧ → G ≈ ⟦ Γ ⟧' ⊘' (⟦ P ⟧ ⊗' ⟦ ⊗⊗ Δ' ⟧)
       τ .{(⟦ Γ F ⟧ ⊘' ⟦ P ⟧) ⊘' ⟦ ⊗⊗ Δ' ⟧} refl = pasc⊘
       t : ⟦ Γ ,,₀ [ P ] ,,₀ [ ⊗⊗ Δ' ] ⟧' ≡ (⟦ Γ ⟧' ⊘' ⟦ P ⟧) ⊘' ⟦ ⊗⊗ Δ' ⟧
       t rewrite sym $ ,,F⊘ (Γ ,,₀ [ P ]) (⊗⊗ Δ') | sym $ ,,F⊘ Γ P = refl

-- Semantics of (more expressive, big ⊗ version of) mix rule

⟦Pmix⟧ : ∀ {Δ Δ₁ Γ Γ₁}{M : Fml - }{N : Fml - } → ctxpol + Δ → ctxpol + Δ₁ → (Γ₁' : ctxpol - Γ₁) →
          Strat - ⟦ M , Γ ,,₀ Δ ⟧' → Strat - ⟦ N ⊗ ⊗⊗ Γ₁' , Δ₁ ⟧' →
            Strat - ⟦  M , Γ ,,₀ N , Γ₁ ,,₀ Δ ,,₀ Δ₁ ⟧'
⟦Pmix⟧ {Δ} {Δ'} {Γ} {Γ₁} {M} {N} Δp Δp' Γ₁' σ τ = σ⊗τ₇
   where σ₁ = (⅋⅋lemma (M , Γ) Δp) ≈∘ σ
         σ₂ : Strat - (⟦ ⅋⅋ Δp ⟧ ⊸ ⟦ M , Γ ⟧')
         σ₂ = subst (λ X → Strat - ⟦ X ⟧) (sym $ ,,F◁ (M , Γ) (⅋⅋ Δp)) σ₁
         τ₁ : Strat - (⟦ ⅋⅋ Δp' ⟧ ⊸ ⟦ N ⟧ ⊗' ⟦ ⊗⊗ Γ₁' ⟧)
         τ₁ = (⅋⅋lemma (N ⊗ ⊗⊗ Γ₁' , ε) Δp') ≈∘ τ
         σ⊗τ₁ : Strat - (⟦ ⅋⅋ Δp ⅋ ⅋⅋ Δp' ⟧ ⊸ ⟦ M , Γ ⟧' ⊘' (⟦ N ⊗ ⊗⊗ Γ₁' ⟧))
         σ⊗τ₁ = (copycat $ ≲wk {⟦ M , Γ ⟧'} {⟦ N ⟧ ⊗' ⟦ ⊗⊗ Γ₁' ⟧}) ∙ (σ₂ ⊗s τ₁)
         σ⊗τ₂ : Strat - (⟦ ⅋⅋ Δp ⅋ ⅋⅋ Δp' ⟧ ⊸ ⟦ (M , Γ) ,,₀ [ N ⊗ ⊗⊗ Γ₁' ] ⟧')
         σ⊗τ₂ rewrite sym $ ,,F⊘ (M , Γ) ( N ⊗ ⊗⊗ Γ₁') = σ⊗τ₁
         σ⊗τ₃ : Strat - (⟦ ⅋⅋ Δp ⅋ ⅋⅋ Δp' ⟧ ⊸ ⟦ M , Γ ,,₀ N , Γ₁ ⟧')
         σ⊗τ₃ = ((⟦ ⅋⅋ Δp ⟧ ⊗' ⟦ ⅋⅋ Δp' ⟧) ⊸≈ (⊗⊗lemma (M , Γ) (N , Γ₁') ^-1)) ≈∘ σ⊗τ₂
         σ⊗τ₄ : Strat - (⟦ ⅋⅋ Δp' ⟧ ⊸ ⟦ (M , Γ ,,₀ N , Γ₁) ,,₀ [ ⅋⅋ Δp ] ⟧')
         σ⊗τ₄ rewrite sym $ ,,F◁ (M , Γ ,,₀ N , Γ₁) (⅋⅋ Δp)
            = (sym⊗ ≈⊸ ⟦ (M , Γ ,,₀ N , Γ₁) ⟧' ≈∘≈ pasc⊸ ^-1) ≈∘ σ⊗τ₃
         σ⊗τ₅ : Strat - (⟦ ⅋⅋ Δp' ⟧ ⊸ ⟦ M , Γ ,,₀ N , Γ₁ ,,₀ Δ ⟧')
         σ⊗τ₅ = (⟦ ⅋⅋ Δp' ⟧ ⊸≈ (⅋⅋lemma (M , Γ ,,₀ N , Γ₁) Δp ^-1) ) ≈∘ σ⊗τ₄
         σ⊗τ₆ : Strat - ⟦ (M , Γ ,,₀ N , Γ₁ ,,₀ Δ ) ,,₀ [ ⅋⅋ Δp' ] ⟧'
         σ⊗τ₆ rewrite sym $ ,,F◁ (M , Γ ,,₀ N , Γ₁ ,,₀ Δ) (⅋⅋ Δp') = σ⊗τ₅
         σ⊗τ₇ : Strat - (⟦ M , Γ ,,₀ N , Γ₁ ,,₀ Δ ,,₀ Δ' ⟧')
         σ⊗τ₇ = (⅋⅋lemma (M , Γ ,,₀ N , Γ₁ ,,₀ Δ) Δp' ^-1) ≈∘ σ⊗τ₆

-- Semantics of Pid⊘

⟦Pid⊘⟧ : ∀ {M N : Fml -} {Q Γ} → ctxpol + Γ → Strat - ⟦ N , Q , Γ ⟧'
             → Strat - ⟦ M , N , (M ⊥') ◁ Q , Γ ⟧'
⟦Pid⊘⟧ {M} {N} {Q} {Γ} Γ₁ σ
    = ⅋⅋lemma (M , N , (M ⊥') ◁ Q , ε) Γ₁ ^-1 ≈∘
      (pasc⊸ ^-1 ≈∘ sym⊗ ≈⊸ _ ≈∘ ≲wk ≲⊸ _ ≲∘ (pasc⊘ ^-1) ≈⊸ _ ≈∘ J (idM ⊘s app)) ∙
      (⅋⅋lemma (N , Q , ε) Γ₁ ≈∘ σ)
    where idM : Strat - (⟦ M ⊥' ⟧ ⊸̂ ⟦ M ⟧)
          idM rewrite ⟦⊥'⟧ M = idσs

-- Semantics of P⊸

⟦P⊸⟧ : ∀ {M : Fml -} {Γ} {P : Fml +} {N} {Δ} → ctxpol + Δ →
       Strat - ⟦ M , Γ ,, P , ε ⟧' → Strat - ⟦ N , Δ ⟧' → Strat - ⟦ M , Γ ,, P ⊘ N , Δ ⟧'
⟦P⊸⟧ {M} {Γ} {P} {N} {Δ} Δ₁ σ τ rewrite sym $ ,,assoc Γ {P ⊘ N , ε} {Δ} | sym $ ,,F◁ (M , Γ) P
   = ⅋⅋lemma (M , Γ ,, P ⊘ N , ε) Δ₁ ^-1 ≈∘ q
   where q : Strat - ⟦ (M , (Γ ,, P ⊘ N , ε) ,, ⅋⅋ Δ₁ , ε) F ⟧
         q rewrite sym $ ,,F◁ (M , (Γ ,, P ⊘ N , ε)) (⅋⅋ Δ₁) | sym $ ,,F◁ (M , Γ) (P ⊘ N)
           = psym⊸ ≈∘ (⅋⅋lemma (N , ε) Δ₁ ≈∘ τ) ⊸s σ

-- Semantics of Pcut0

⟦Pcut0⟧ : ∀ {N : Fml -} {Q : Fml +} → Strat + ⟦ N ⊥' , ε ⟧' → Strat - ⟦ N , Q , ε ⟧' → Strat + ⟦ Q , ε ⟧'
⟦Pcut0⟧ {N} {Q} p q rewrite ⟦⊥'⟧ N = unσ⊸o $ ↑≈⊸o ^-1 ≈∘ (↑≈⊸o ≈∘ (σ⊸o p)) ∙ q
