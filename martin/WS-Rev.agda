module WS-Rev where
-- depreciated

open import Data.Bool renaming (true to - ; false to +; Bool to Pol; not to ¬)
open import Data.Product renaming (,_ to `_)
open import Data.Function
open import Relation.Binary.PropositionalEquality

open import WS-Syn
open import WS-Sem-Fsc

-- Reversibility

infix 3 ⊢c_
data ⊢c_ : ∀ {p} → Seq p → Set where
  P1  : ∀ {Γ} → ⊢c F1 , Γ
  P⊗  : ∀ {M N Γ} → ⊢c M , N , Γ → ⊢c N , M , Γ → ⊢c M ⊗ N , Γ
  P⅋₁ : ∀ {P Q Γ} → ⊢c P , Q , Γ → ⊢c P ⅋ Q , Γ
  P⅋₂ : ∀ {P Q Γ} → ⊢c Q , P , Γ → ⊢c P ⅋ Q , Γ
  P⊕₁ : ∀ {P Q Γ} → ⊢c P , Γ → ⊢c P ⊕ Q , Γ
  P⊕₂ : ∀ {P Q Γ} → ⊢c Q , Γ → ⊢c P ⊕ Q , Γ
  P&  : ∀ {M N Γ} → ⊢c M , Γ → ⊢c N , Γ → ⊢c M & N , Γ
  P↑  : ∀ {P}     → ⊢c P , ε → ⊢c ↑ P , ε
  P↑- : ∀ {P N Γ} → ⊢c ↑(P ⊘ N) , Γ → ⊢c ↑ P , N , Γ
  P↑+ : ∀ {P Q Γ} → ⊢c ↑(P ⅋ Q) , Γ → ⊢c ↑ P , Q , Γ
  P↓  : ∀ {N}     → ⊢c N , ε → ⊢c ↓ N , ε
  P↓+ : ∀ {N P Γ} → ⊢c ↓(N ◁ P) , Γ → ⊢c ↓ N , P , Γ
  P↓- : ∀ {M N Γ} → ⊢c ↓(M ⊗ N) , Γ → ⊢c ↓ M , N , Γ
  P⊘  : ∀ {p}{A : Fml p}{M Γ} → ⊢c A , M , Γ → ⊢c A ⊘ M , Γ
  P◁  : ∀ {p}{A : Fml p}{P Γ} → ⊢c A , P , Γ → ⊢c A ◁ P , Γ

unP◁ : ∀{p}{A : Fml p}{P Γ} → ⊢c A ◁ P , Γ → ⊢c A , P , Γ
unP◁ (P◁ h) = h

unP⊘ : ∀{p}{A : Fml p}{M Γ} → ⊢c A ⊘ M , Γ → ⊢c A , M , Γ
unP⊘ (P⊘ h) = h

P⊘◁s : ∀ {p}{H : Fml p}(Γ : Ctx){Δ} → ⊢c H , Γ ,, Δ → ⊢c (H , Γ) F , Δ
P⊘◁s ε p' = p'
P⊘◁s (_,_ { - } y y') p0 = P⊘◁s y' (P⊘ p0)
P⊘◁s (_,_ { + } y y') p0 = P⊘◁s y' (P◁ p0)

unP◁⊘Fs : ∀ {p}(Γ : Seq p){Δ} → ⊢c Γ F , Δ → ⊢c Γ ,,₀ Δ
unP◁⊘Fs (A , ε             ) h = h
unP◁⊘Fs (A , _,_ { + } P  Γ) h = unP◁ (unP◁⊘Fs (A ◁ P , Γ) h)
unP◁⊘Fs (A , _,_ { - } M  Γ) h = unP⊘ (unP◁⊘Fs (A ⊘ M , Γ) h)

_↑F : Seq + → Fml +
(P , ε) ↑F = P
(P , (_,_ { - } M Γ)) ↑F = (P ⊘ M , Γ) ↑F
(P , (_,_ { + } Q Γ)) ↑F = (P ⅋ Q , Γ) ↑F

_↓F : Seq - → Fml -
(N , ε) ↓F = N
(N , (_,_ { - } M Γ)) ↓F = (N ⊗ M , Γ) ↓F
(N , (_,_ { + } Q Γ)) ↓F = (N ◁ Q , Γ) ↓F

P↑Fs : ∀ { H } (Γ : Ctx) { Δ } → ⊢c ↑ ((H , Γ) ↑F) , Δ →  ⊢c ↑ H , Γ ,, Δ 
P↑Fs ε p = p
P↑Fs (_,_ { + } P Γ) {Δ} p' = P↑+ (P↑Fs Γ p')
P↑Fs (_,_ { - } N Γ) {Δ} p' = P↑- (P↑Fs Γ p')

P↓Fs : ∀ { H } (Γ : Ctx) { Δ } → ⊢c ↓ ((H , Γ) ↓F) , Δ →  ⊢c ↓ H , Γ ,, Δ 
P↓Fs ε p = p
P↓Fs (_,_ { + } P Γ) {Δ} p' = P↓+ (P↓Fs Γ p')
P↓Fs (_,_ { - } N Γ) {Δ} p' = P↓- (P↓Fs Γ p')

unP↑+ : ∀{P Q Γ} → ⊢c ↑ P , Q , Γ → ⊢c ↑ (P ⅋ Q) , Γ
unP↑+ (P↑+ h) = h

unP↑- : ∀{P M Γ} → ⊢c ↑ P , M , Γ → ⊢c ↑ (P ⊘ M) , Γ
unP↑- (P↑- h) = h

unP↑Fs : ∀ { H } (Γ : Ctx) { Δ } → ⊢c ↑ H , Γ ,, Δ → ⊢c ↑ ((H , Γ) ↑F) , Δ
unP↑Fs ε h = h
unP↑Fs {H} (_,_ { + } A Γ) h = unP↑Fs Γ (unP↑+ h)
unP↑Fs {H} (_,_ { - } A Γ) h = unP↑Fs Γ (unP↑- h)

unP↓- : ∀{P Q Γ} → ⊢c ↓ P , Q , Γ → ⊢c ↓ (P ⊗ Q) , Γ
unP↓- (P↓- h) = h

unP↓+ : ∀{P M Γ} → ⊢c ↓ M , P , Γ → ⊢c ↓ (M ◁ P) , Γ
unP↓+ (P↓+ h) = h

unP↓Fs : ∀ { H } (Γ : Ctx) { Δ } → ⊢c ↓ H , Γ ,, Δ → ⊢c ↓ ((H , Γ) ↓F) , Δ
unP↓Fs ε h = h
unP↓Fs {H} (_,_ { - } A Γ) h = unP↓Fs Γ (unP↓- h)
unP↓Fs {H} (_,_ { + } A Γ) h = unP↓Fs Γ (unP↓+ h)

unP↑ : ∀ {P} → ⊢c ↑ P , ε → ⊢c P , ε
unP↑ (P↑ p) = p

unP↓ : ∀ {N} → ⊢c ↓ N , ε → ⊢c N , ε
unP↓ (P↓ p) = p
