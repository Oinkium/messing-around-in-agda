module WS-FinCount where
-- in which we give an example of an imperative object as a proof in
-- WS (specifically, a counter object)

open import Data.Function
--open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_+_ to _+'_)

open import WS-Syn

! : ℕ → Fml - → Fml -
! zero    M = F1
! (suc n) M = M ⊘ ! n M

⊕ℕ : ℕ → Fml +
⊕ℕ zero    = ↓ F1
⊕ℕ (suc n) = ↓ F1 ⊕ (⊕ℕ n) 

Gℕf : ℕ → Fml -
Gℕf n = ↑ (⊕ℕ n)

ΣF : Fml -
ΣF = ↑ (↓ F1)

Σn : ℕ → Fml -
Σn n = ! n ΣF

counttype : ℕ → Fml -
counttype n = Σn n ⊗ Gℕf n

comn : ∀ n → ⊢ Σn n , ε
comn (zero)  = P1
comn (suc n) = P⊘ $ P↑- $ P↑ $ P⊘ $ P↓- $ P↓ $ P⊗ P1 $ P1T {Γ = ! n (↑ (↓ F1)) , ε} $ comn n

≤′lem : ∀ {n} {m} → suc n ≤′ m → n ≤′ m
≤′lem ≤′-refl        = ≤′-step $ ≤′-refl
≤′lem (≤′-step m≤′n) = ≤′-step $ ≤′lem m≤′n

mutual
    count₁ : (n m : ℕ) → n ≤′ m → ⊢ ! n (↑ (↓ F1)) , ↑ (⊕ℕ m) , ε
    count₁ zero    _ _  = P1
    count₁ (suc n) m le = P⊘ $ P↑- $ P↑- $ P↑ $ P⊘ $ P⊘ $ P↓- $ P↓- $ P↓ $ P⊗
                 (P⊗ P1 $ P1T {Γ = ! n (↑ (↓ F1)) , ε} $ count₁ n m $ ≤′lem le)
                 (P⊗T {Γ = ↑ (⊕ℕ m) , ε} $ P1T {Γ = ↑ (⊕ℕ m) , ε} $ 
                   P↑- $ P↑ $ P⊘ $ count₃ n m $ ≤′lem le)

    count₃ : (n m : ℕ) → n ≤′ m → ⊢ ⊕ℕ m , ! n (↑ (↓ F1)) , ε
    count₃ zero    .zero    ≤′-refl      = P↓- $ P↓ $ P⊗ P1 P1
    count₃ (suc n) .(suc n) ≤′-refl      = P⊕₁ $ P↓- $ P↓ $ P⊗ P1
                       $ P1T {Γ = ↑ (↓ F1) ⊘ ! n (↑ (↓ F1)) , ε} $ comn (suc n)
    count₃ n        (suc m) (≤′-step le) = P⊕₂ (count₃ n m le)

count : ∀ n → ⊢ [ counttype n ]'
count n = P⊗ (count₁ n n ≤′-refl) (P↑- $ P↑ $ P⊘ $ count₃ n n ≤′-refl)

!⊗ : ℕ → Fml - → Fml -
!⊗ zero M = F1
!⊗ (suc n) M = M ⊗ !⊗ n M

multicount_type : ℕ → ℕ → Fml -
multicount_type m n = !⊗ m (counttype n)

multicount : ∀ m n → ⊢ [ multicount_type m n ]'
multicount zero n     = P1
multicount (suc n) n' = P⊗
           (Pmix {ε} ε ε ε (count n') $ P⊗
                    (P1T {Γ = [ multicount n type n' ]'} ((multicount n n')))
                    P1)
           (Pmix {ε} ε ε ε (multicount n n') $ P⊗
                    (P1T {Γ = [ counttype n' ]'} (count n')) 
                    P1)

readcounter : ∀ n → ⊢ Gℕf n , [ (counttype n) ⊥' ]
readcounter n = P⅋T {Γ = [ Gℕf n ]'} (Pstr {Γ = [ Gℕf n ]'} Pid)

shouldbezero : ∀ n → ⊢ [ Gℕf n ]'
shouldbezero n = P1Tb {Γ = [ Gℕf n ]'} (Pcut {Γ = [ Gℕf n ]'} {counttype n} ε (P1T {Γ = ↑ (⊕ℕ n) , [ (! n (↑ (↓ F1)) ⊥') ⅋ ↓ (⊕ℕ n ⊥') ]} (readcounter n)) (count n))
