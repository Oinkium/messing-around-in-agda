module WS-Sem where
-- in which we give semantics to proofs of WS as strategies

open import Function
open import Relation.Binary.PropositionalEquality

open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import WS-Syn public
open import WS-Sem-Fsc public
open import WS-Sem-Core
open import WS-Sem-Tails
open import WS-Sem-Adm

⟦_⟧⊢ : ∀ {p}{Γ : Seq p} → ⊢ Γ → Strat p ⟦ Γ ⟧'
⟦_⟧⊢ {.p} {._} (P1T {p} {Γ} {Δ} y)              = ⟦P1T⟧  {p} {Δ} {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ P⊤                                         = ⟦P⊤⟧
⟦_⟧⊢ {.p} {._} (P0T {p} {Γ} {Δ} y)              = ⟦P0T⟧  {p} {Δ} {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (P⊗T {p} {M} {N} {Δ} {Γ} y)      = ⟦P⊗T⟧  {p} {M} {N} {Δ} {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (P⅋T {p} {M} {N} {Δ} {Γ} y)      = ⟦P⅋T⟧  {p} {M} {N} {Δ} {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (P1Tb {p} {Γ} {Δ} y)             = ⟦P1Tb⟧ {p} {Δ} {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (P0Tb {p} {Γ} {Δ} y)             = ⟦P0Tb⟧ {p} {Δ} {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (P⊗Tb {p} {M} {N} {Δ} {Γ} y)     = ⟦P⊗Tb⟧ {p} {M} {N} {Δ} {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (P⅋Tb {p} {M} {N} {Δ} {Γ} y)     = ⟦P⅋Tb⟧ {p} {M} {N} {Δ} {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (P⊕T₁ {p} {P} {Q} {Δ} {Γ} y)     = ⟦P⊕T₁⟧ {p} {P} {Q} {Δ} {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (P⊕T₂ {p} {P} {Q} {Δ} {Γ} y)     = ⟦P⊕T₂⟧ {p} {P} {Q} {Δ} {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (P⊕Tω {p} {P} {Δ} {Γ} n y)       = ⟦P⊕Tω⟧ {p} {P} {Δ} {Γ} n ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (Psym {p} {q} {Δ} {Γ} {A} {B} y) = ⟦Psym⟧ {p} {q} {Δ} {Γ} {A} {B} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (Pstr {p} {Δ} {Γ} {P} y)         = ⟦Pstr⟧ {p} {Δ} {Γ} {P} ⟦ y ⟧⊢
⟦_⟧⊢ {.p} {._} (Pwk {p} {Δ} {Γ} {P} y)          = ⟦Pwk⟧  {p} {Δ} {Γ} {P} ⟦ y ⟧⊢
⟦_⟧⊢ {. - } {._} (Pid {M})                      = ⟦Pid⟧  {M}
⟦_⟧⊢ {. - } {._} (Pmix {Γ} {Δ} {Δ₁} {Γ₁} {N} {M} y y' Γ₁' y0 y1)
         = ⟦Pmix⟧ {Δ} {Δ₁} {Γ} {Γ₁} {M} {N} y y' Γ₁' ⟦ y0 ⟧⊢ ⟦ y1 ⟧⊢
⟦_⟧⊢ {. - } {._} (P⊸ {M} {Γ} {P} {N} {Δ} Δ₁ y0 y1)
         = ⟦P⊸⟧ {M} {Γ} {P} {N} {Δ} Δ₁ ⟦ y0 ⟧⊢ ⟦ y1 ⟧⊢
⟦_⟧⊢ {. - } {._} (Pid⊘ {M} {N} {Q} {Γ} Γ₁ σ)
         = ⟦Pid⊘⟧ {M} {N} {Q} {Γ} Γ₁ ⟦ σ ⟧⊢
⟦_⟧⊢ {.p} {._} (Pcut {p} {Δ} {Γ₁} {Γ} {M} Δp y y')
         = ⟦Pcut⟧ {p} {Δ} {Γ₁} {Γ} {M} Δp ⟦ y ⟧⊢ ⟦ y' ⟧⊢
⟦_⟧⊢ {. + } {._} (Pcut0 {N} {Q} y y')           = ⟦Pcut0⟧ {N} {Q} ⟦ y ⟧⊢ ⟦ y' ⟧⊢
⟦_⟧⊢ {. - } {Γ = F1 , Γ } P1                    = ⟦P1⟧   {Γ}
⟦_⟧⊢ {. - } {Γ = M ⊗ N , Γ } (P⊗ y y')          = ⟦P⊗⟧   {Γ} ⟦ y ⟧⊢ ⟦ y' ⟧⊢
⟦_⟧⊢ {. + } {Γ = P ⅋ Q , Γ } (P⅋₁ y)            = ⟦P⅋1⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {. + } {Γ = P ⅋ Q , Γ } (P⅋₂ y)            = ⟦P⅋2⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {. + } {Γ = P ⊕ Q , Γ } (P⊕₁ y)            = ⟦P⊕1⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {. + } {Γ = P ⊕ Q , Γ } (P⊕₂ y)            = ⟦P⊕2⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {. + } {Γ = ω⊕ P , Γ } (P⊕ω n y)           = ⟦P⊕ω⟧  {Γ} n ⟦ y ⟧⊢
⟦_⟧⊢ {. - } {Γ = M & N , Γ } (P& y y')          = ⟦P&⟧   {Γ} ⟦ y ⟧⊢ ⟦ y' ⟧⊢
⟦_⟧⊢ {. - } {Γ = ω& M , Γ } (P&ω f)             = ⟦P&ω⟧  {Γ} (λ y → ⟦ f y ⟧⊢)
⟦_⟧⊢ {_} {Γ = A ⊘ M , Γ } (P⊘ y)                = ⟦P⊘⟧   {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {_} {Γ = A ◁ P , Γ } (P◁ y)                = ⟦P◁⟧   {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {. - } {Γ = F⊥ , P , ε } (P⊥+ y)            = ⟦P⊥+⟧   {P} ⟦ y ⟧⊢
⟦_⟧⊢ {. - } {Γ = F⊥ , N , Γ } (P⊥- y)            = ⟦P⊥-⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {. - } {Γ = F⊥ , P , M , Γ } (P⊥⊘ y)        = ⟦P⊥⊘⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {. - } {Γ = F⊥ , P , Q , Γ } (P⊥⅋ y)        = ⟦P⊥⅋⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {. + } {Γ = F⊤ , N , ε } (P⊤- y)            = ⟦P⊤-⟧  {N} ⟦ y ⟧⊢
⟦_⟧⊢ {. + } {Γ = F⊤ , P , Γ } (P⊤+ y)            = ⟦P⊤+⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {. + } {Γ = F⊤ , N , P , Γ } (P⊤◁ y)        = ⟦P⊤◁⟧  {Γ} ⟦ y ⟧⊢
⟦_⟧⊢ {. + } {Γ = F⊤ , N , M , Γ } (P⊤⊗ y)        = ⟦P⊤⊗⟧  {Γ} ⟦ y ⟧⊢

--⟦_⟧⊢ {. - } {._} (P⊥ {p} {Γ} y)                 = ⟦P⊥⟧   {p} {Γ} ⟦ y ⟧⊢
--⟦_⟧⊢ {. + } {._} (P⊤ {p} {Γ} y)                 = ⟦P⊤⟧   {p} {Γ} ⟦ y ⟧⊢
--⟦_⟧⊢ {. - } {._} (P⊥b {p} {Γ} y)                = ⟦P⊥b⟧  {p} {Γ} ⟦ y ⟧⊢
--⟦_⟧⊢ {. + } {._} (P⊤b {p} {Γ} y)                = ⟦P⊤b⟧  {p} {Γ} ⟦ y ⟧⊢
--⟦_⟧⊢ {_} (P⊘b y)                                = ⟦ y ⟧⊢
--⟦_⟧⊢ {_} (P◁b y)                                = ⟦ y ⟧⊢