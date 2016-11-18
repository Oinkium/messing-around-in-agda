module WS-Exp where
-- in which we embed bounded sequoidal exponentials and operations
-- thereupon in WS

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_+_ to _+'_)
open import Data.Product
open import Data.Nat.Properties
open import Algebra.Structures
open IsCommutativeSemiring isCommutativeSemiring using (+-assoc ; +-comm ; *-comm)
open import Data.Bool

open import WS-Syn

-- The Bounded Exponential

! : ℕ → Fml - → Fml -
! zero    M = F1
! (suc n) M = M ⊘ ! n M

-- The following definitions are given by induction on n. But they can
-- be adapted to the general, infinitary sequoidal exponential, by
-- changing the induction on n to a formal least fixed point, using
-- the minimal invariance property.

-- Promotion

⊗! : ∀ n N → ⊢ ! n N ⊗ N , ! (suc n) N ⊥' , ε
⊗! zero N = P⊗ P1 (Pid⊘ ε P1)
⊗! (suc n) N = P⊗ (P⊘ $ P⊗Tb {Γ = [ N ]'} $ Pid⊘ ε $ ⊗! n N) (Pid⊘ ε Pid)

prom : ∀ n M N → ⊢ M , N ⊥' , ε → ⊢ ! n M , (! n N) ⊥' , ε
prom zero M N p = P1
prom (suc n) M N p = Pcut {Γ = [ M ⊘ ! n M ]'} ((N ⊥') ◁ (! n N ⊥') , ε)
                      (P⅋T {Γ = [ M ⊘ ! n M ]'} $ Psym {Γ = [ M ⊘ ! n M ]'} $ P⊘ $
                         Pmix {Γ = ε} (N ⊥' , ε) (! n N ⊥' , ε) ε p $
                           P⊗ (P1T {Γ = [ ! n M ]'} $ prom n M N p) P1)
                      (⊗! n N)

-- Dereliction

derel : ∀ A → ⊢ A , ! 1 A ⊥' , ε 
derel A = P1Tb {Γ = [ A ]'} $ Pid⊘ ε P1

bang0 : ∀ n → ⊢ ! n F1 , F0 , ε
bang0 zero = P1
bang0 (suc n) = P⊘ $ P1

-- Contraction

mutual
  contr₁ : ∀ n m A → ⊢ ! n A , ! m A , (! (n +' m) A) ⊥' , ε
  contr₁ zero m A = P1
  contr₁ (suc n) m A = P⊘ $ P⊗Tb {Γ = [ A ]'} $ Pid⊘ ε $ contr n m A

  contr₂ : ∀ n m A → ⊢ ! m A , ! n A , (! (n +' m) A) ⊥' , ε
  contr₂ n m A rewrite +-comm n m = contr₁ m n A

  contr : ∀ n m A → ⊢ ! n A ⊗ ! m A , (! (n +' m) A) ⊥' , ε
  contr n m A = P⊗ (contr₁ n m A) (contr₂ n m A)

-- Multiplication

!mult : ∀ n m A → ⊢ (! n (! m A)), [ ! (n * m) A ⊥' ]
!mult zero m A = P1
!mult (suc n) m A = Pcut {Γ = [ ! m A ⊘ ! n (! m A) ]'} (! (m +' (n * m)) A ⊥' , ε)
        (P⊘ $ P⅋T {Γ = ! m A , ! n (! m A) , ε} $ Pmix {Γ = ε} (! m A ⊥' , ε)
             (! (n * m) A ⊥' , ε) ε Pid (P⊗
                           (P1T {Γ = [ ! n (! m A) ]'} $ !mult n m A)
                            P1))
        (contr m (n * m) A)

!mult' : ∀ n m A → ⊢ (! n (! m A)), [ ! (m * n) A ⊥' ]
!mult' n m A rewrite *-comm m n = !mult n m A

-- Monoidalness

!monoidal : ∀ n M N → ⊢ ! n (M ⊗ N) , ! n M ⊥' , ! n N ⊥' , ε
!monoidal zero M N = P1
!monoidal (suc n) M N = Pcut {Γ = [ ! (suc n) (M ⊗ N) ]'} (! (suc n) M ⊥' , ε)
                        (P⅋T {Γ = [ ! (suc n) (M ⊗ N) ]'} $
                         Pcut {Γ = ! (suc n) (M ⊗ N) , ! n M ⊥' , M ⊥' , ε} (! (suc n) N ⊥' , ε)
                             (P⅋T {Γ = ! (suc n) (M ⊗ N) , ! n M ⊥' , M ⊥' , ε} $ P⊘ $
                              Psym {Γ = M ⊗ N , ! n (M ⊗ N) , ε} $
                              Psym {Γ = M ⊗ N , ! n (M ⊗ N) , M ⊥' , ! n M ⊥' , ε} $
                              Psym {Γ = M ⊗ N , ! n (M ⊗ N) , M ⊥' , ε} $
                              P⅋Tb {Γ = M ⊗ N , ! n (M ⊗ N) , ε} $
                              P⅋Tb {Γ = M ⊗ N , ! n (M ⊗ N) , M ⊗ N ⊥' , ε} $
                              Pmix {Γ = ε} (M ⊗ N ⊥' , ε) (! n M ⊗ ! n N ⊥' , ε) ε Pid $
                              P⊗ (P1T {Γ = [ ! n (M ⊗ N) ]'} $
                                  P⅋T {Γ = [ ! n (M ⊗ N) ]'} $
                                  !monoidal n M N)
                              P1)
                        (⊗! n N))
                     (⊗! n M)

-- Increment

!incr : ∀ n m A → ⊢ ! n A , [ ! (n +' m) A ⊥' ]
!incr n m A = Pcut {Γ = [ ! n A ]'} (! (n +' m) A ⊥' , ε)
            (P⅋T {Γ = [ ! n A ]'} $ Pstr {Γ = ! n A , ! n A ⊥' , ε} Pid)
            (contr n m A)
