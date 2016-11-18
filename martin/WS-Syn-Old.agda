module WS-Syn where
-- in which we define the syntax of WS.

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Nat renaming (_+_ to _+'_)

-- Polarities

-- Polarities are just renamed Booleans.
open import Data.Bool public
   renaming (true to -  ; false to +;
             Bool to Pol; not   to ¬;
             T to isTrue)

idem¬ : ∀ {p} → ¬ (¬ p) ≡ p
idem¬ { + } = refl
idem¬ { - } = refl

-- Formulas of WS

data Fml : Pol → Set where
  F0  : Fml +
  F1  : Fml -
  ↑   : (P : Fml +) → Fml -
  ↓   : (M : Fml -) → Fml +
  _⊗_ : (M N : Fml -) → Fml -
  _⅋_ : (P Q : Fml +) → Fml +
  _⊕_ : (P Q : Fml +) → Fml +
  _&_ : (M N : Fml -) → Fml -
  _⊘_ : ∀ {p} → (A : Fml p) (M : Fml -) → Fml p
  _◁_ : ∀ {p} → (A : Fml p) (P : Fml +) → Fml p
  ω&  : (M : Fml -) → Fml -
  ω⊕  : (P : Fml +) → Fml +

-- Opposite of Formulas

infix 8 _⊥'

_⊥' : {p : Pol} → Fml p → Fml (¬ p)
F0      ⊥' = F1
F1      ⊥' = F0
(↑ P)   ⊥' = ↓ (P ⊥')
(↓ N)   ⊥' = ↑ (N ⊥')
(M ⊗ N) ⊥' = (M ⊥') ⅋ (N ⊥')
(P ⅋ Q) ⊥' = (P ⊥') ⊗ (Q ⊥')
(A ⊘ M) ⊥' = (A ⊥') ◁ (M ⊥')
(A ◁ P) ⊥' = (A ⊥') ⊘ (P ⊥')
(P ⊕ Q) ⊥' = (P ⊥') & (Q ⊥')
(M & N) ⊥' = (M ⊥') ⊕ (N ⊥') 
(ω& M)  ⊥' = ω⊕ (M ⊥')
(ω⊕ P)  ⊥' = ω& (P ⊥')

-- We now show idem⊥f is idempotent. RHS is just P --- but we need to
-- use idem¬ for the statement to typecheck.

idem⊥f : ∀ {p} (P : Fml p) → (P ⊥') ⊥' ≡ (subst Fml (sym idem¬)) P
idem⊥f        F0     = refl
idem⊥f        F1     = refl
idem⊥f       (↑ P)   = cong ↑ (idem⊥f P)
idem⊥f       (↓ M)   = cong ↓ (idem⊥f M)
idem⊥f       (M ⊗ N) = cong₂ _⊗_ (idem⊥f M) (idem⊥f N)
idem⊥f       (P ⅋ Q) = cong₂ _⅋_ (idem⊥f P) (idem⊥f Q)
idem⊥f { - } (M ⊘ N) = cong₂ _⊘_ (idem⊥f M) (idem⊥f N)
idem⊥f { + } (P ⊘ N) = cong₂ _⊘_ (idem⊥f P) (idem⊥f N)
idem⊥f { - } (M ◁ P) = cong₂ _◁_ (idem⊥f M) (idem⊥f P)
idem⊥f { + } (P ◁ Q) = cong₂ _◁_ (idem⊥f P) (idem⊥f Q)
idem⊥f       (P ⊕ Q) = cong₂ _⊕_ (idem⊥f P) (idem⊥f Q)
idem⊥f       (M & N) = cong₂ _&_ (idem⊥f M) (idem⊥f N)
idem⊥f       (ω& M)  = cong ω& (idem⊥f M)
idem⊥f       (ω⊕ P)  = cong ω⊕ (idem⊥f P)

-- Contexts

-- A context is a list of formulas of any polarity.

infixr 7 _,_

data Ctx : Set where
  ε   : Ctx
  _,_ : ∀ {p} → Fml p → Ctx → Ctx

infix 8 [_]
[_] : ∀ {p} → Fml p → Ctx
[ A ] = A , ε

-- Concatenation of contexts, and its properties.

infixr 7 _,,_
_,,_ : Ctx → Ctx → Ctx
ε       ,, Δ = Δ
(A , Γ) ,, Δ = A , Γ ,, Δ

,,assoc : ∀ Γ { Δ Ε } → (Γ ,, Δ) ,, Ε ≡ Γ ,, (Δ ,, Ε)
,,assoc ε       = refl
,,assoc (A , Γ) = cong (_,_ A) (,,assoc Γ)

,,ε : ∀ Δ → Δ ,, ε ≡ Δ
,,ε ε       = refl
,,ε (A , Δ) = cong (λ X → A , X) (,,ε Δ)

-- Sequents

-- A sequent is a nonempty list of formulas of either polarity.
-- It is convinient to parameterise sequents by the polarity of
-- their head formula. 

data Seq(p : Pol) : Set where
  _,_ : Fml p → Ctx → Seq p

infix 8 [_]'
[_]' : ∀ {p} → Fml p → Seq p
[ A ]' = A , ε

-- Concatenation of sequents and contexts, and their properties.

infixl 7 _,,₀_
_,,₀_ : ∀ {p} → Seq p → Ctx → Seq p
(A , Γ) ,,₀ Δ = A , (Γ ,, Δ)

,,₀ε : ∀ {p}(Γ : Seq p) → Γ ,,₀ ε ≡ Γ
,,₀ε (A , Δ) = cong (λ X → A , X) (,,ε Δ)

,,₀assoc : ∀ {p}(Γ : Seq p){Δ Ε} → (Γ ,,₀ Δ) ,,₀ Ε ≡ Γ ,,₀ (Δ ,, Ε)
,,₀assoc (A , Γ) = cong (_,_ A) (,,assoc Γ)

-- Predicate: ctxpol p Δ holds if all elements in Δ have polarity p.

data ctxpol (p : Pol) : Ctx → Set where
  ε   : ctxpol p ε
  _,_ : ∀ {Γ} → (P : Fml p) → ctxpol p Γ → ctxpol p (P , Γ)

-- Taking the ⊗ of a list of negative formulas.

⊗⊗ : ∀ {Γ} → ctxpol - Γ → Fml -
⊗⊗ ε       = F1
⊗⊗ (P , y) = P ⊗ (⊗⊗ y)

-- Proof rules of WS

infix 3 ⊢_
data ⊢_ : ∀ {p} → Seq p → Set where
  -- Core rules:
  P1  : ∀ {Γ} → ⊢ F1 , Γ
  P⊗  : ∀ {M N Γ} → ⊢ M , N , Γ → ⊢ N , M , Γ → ⊢ M ⊗ N , Γ
  P&  : ∀ {M N Γ} → ⊢ M , Γ → ⊢ N , Γ → ⊢ M & N , Γ
  P&ω : ∀ {M Γ}   → (ℕ → ⊢ M , Γ) → ⊢ ω& M , Γ
  P↑  : ∀ {P}     → ⊢ P , ε → ⊢ ↑ P , ε
  P↑- : ∀ {P N Γ} → ⊢ ↑(P ⊘ N) , Γ → ⊢ ↑ P , N , Γ
  P↑+ : ∀ {P Q Γ} → ⊢ ↑(P ⅋ Q) , Γ → ⊢ ↑ P , Q , Γ
  P⅋₁ : ∀ {P Q Γ} → ⊢ P , Q , Γ → ⊢ P ⅋ Q , Γ
  P⅋₂ : ∀ {P Q Γ} → ⊢ Q , P , Γ → ⊢ P ⅋ Q , Γ
  P⊕₁ : ∀ {P Q Γ} → ⊢ P , Γ → ⊢ P ⊕ Q , Γ
  P⊕₂ : ∀ {P Q Γ} → ⊢ Q , Γ → ⊢ P ⊕ Q , Γ
  P⊕ω : ∀ {P Γ}   → ℕ → ⊢ P , Γ → ⊢ ω⊕ P , Γ 
  P↓  : ∀ {N}     → ⊢ N , ε → ⊢ ↓ N , ε
  P↓+ : ∀ {N P Γ} → ⊢ ↓(N ◁ P) , Γ → ⊢ ↓ N , P , Γ
  P↓- : ∀ {M N Γ} → ⊢ ↓(M ⊗ N) , Γ → ⊢ ↓ M , N , Γ
  P⊘  : ∀ {p}{A : Fml p}{M Γ} → ⊢ A , M , Γ → ⊢ A ⊘ M , Γ
  P◁  : ∀ {p}{A : Fml p}{P Γ} → ⊢ A , P , Γ → ⊢ A ◁ P , Γ
  -- Other rules:
  P⊘b : ∀ {p}{A : Fml p}{M Γ} → ⊢ A ⊘ M , Γ → ⊢ A , M , Γ
  P◁b : ∀ {p}{A : Fml p}{P Γ} → ⊢ A ◁ P , Γ → ⊢ A , P , Γ
  P1T  : ∀ {p}{Γ : Seq p}{Δ} → ⊢ Γ ,,₀ Δ → ⊢ Γ ,,₀ F1 , Δ
  P1Tb : ∀ {p}{Γ : Seq p}{Δ} → ⊢ Γ ,,₀ F1 , Δ → ⊢ Γ ,,₀ Δ
  P0T  : ∀ {p}{Γ : Seq p}{Δ} → ⊢ Γ ,,₀ Δ → ⊢ Γ ,,₀ F0 , Δ
  P0Tb : ∀ {p}{Γ : Seq p}{Δ} → ⊢ Γ ,,₀ F0 , Δ → ⊢ Γ ,,₀ Δ
  P⊥   : ∀ {P Γ} → ⊢ ↑ P , Γ → ⊢ ↑ F0 , P , Γ
  P⊥b  : ∀ {P Γ} → ⊢ ↑ F0 , P , Γ → ⊢ ↑ P , Γ
  P⊤   : ∀ {N Γ} → ⊢ ↓ N , Γ → ⊢ ↓ F1 , N , Γ
  P⊤b  : ∀ {N Γ} → ⊢ ↓ F1 , N , Γ → ⊢ ↓ N , Γ
  P⊗T  : ∀ {p M N Δ} {Γ : Seq p} → ⊢ Γ ,,₀ M , N , Δ → ⊢ Γ ,,₀ M ⊗ N , Δ
  P⊗Tb : ∀ {p M N Δ} {Γ : Seq p} → ⊢ Γ ,,₀ M ⊗ N , Δ → ⊢ Γ ,,₀ M , N , Δ
  P⅋T  : ∀ {p P Q Δ} {Γ : Seq p} → ⊢ Γ ,,₀ P , Q , Δ → ⊢ Γ ,,₀ P ⅋ Q , Δ
  P⅋Tb : ∀ {p P Q Δ} {Γ : Seq p} → ⊢ Γ ,,₀ P ⅋ Q , Δ → ⊢ Γ ,,₀ P , Q , Δ
  P⊕T₁ : ∀ {p P Q Δ} {Γ : Seq p} → ⊢ Γ ,,₀ P , Δ → ⊢ Γ ,,₀ P ⊕ Q , Δ
  P⊕T₂ : ∀ {p P Q Δ} {Γ : Seq p} → ⊢ Γ ,,₀ Q , Δ → ⊢ Γ ,,₀ P ⊕ Q , Δ
  P⊕Tω : ∀ {p P Δ} {Γ : Seq p}   → ℕ → ⊢ Γ ,,₀ P , Δ → ⊢ Γ ,,₀ ω⊕ P , Δ 
  Psym : ∀ {p q Δ} {Γ : Seq p} {A B : Fml q} →
          ⊢ Γ ,,₀ A , B , Δ → ⊢ Γ ,,₀ B , A , Δ
   Pstr : ∀ {p Δ}  {Γ : Seq p}{P : Fml + } → ⊢ Γ ,,₀ Δ     → ⊢ Γ ,,₀ P , Δ
   Pwk  : ∀ {p Δ}  {Γ : Seq p}{M : Fml - } → ⊢ Γ ,,₀ M , Δ → ⊢ Γ ,,₀ Δ
  Pcut : ∀ {p Δ Γ₁}{Γ : Seq p}{M : Fml - } → ctxpol + Δ →
          ⊢ Γ ,,₀ M ⊥' , Γ₁ → ⊢ M , Δ → ⊢ Γ ,,₀ Δ ,,₀ Γ₁
  Pid  : ∀ {M : Fml - } → ⊢ M , M ⊥' , ε
  Pmix : ∀ {Γ Δ Δ₁ Γ₁ N}{M : Fml -} → ctxpol + Δ → ctxpol + Δ₁
          → (Γ₁' : ctxpol - Γ₁)
          → ⊢ M , Γ ,,₀ Δ → ⊢ N ⊗ (⊗⊗ Γ₁') , Δ₁
          → ⊢ M , Γ ,,₀ N , Γ₁ ,,₀ Δ ,,₀ Δ₁
  Pid⊘ : ∀ {M N : Fml -} {Q Γ} → ctxpol + Γ → ⊢ N , Q , Γ →
          ⊢ M , N , (M ⊥') ◁ Q , Γ
 
PolFml : Set
PolFml = Σ Pol Fml

PolSeq : Set
PolSeq = Σ Pol Seq

infix 2 _⊣:_
data Prf : Set where
  _⊣:_ : ∀ {pol}(Γ : Seq pol)(pf : ⊢ Γ) → Prf

