module WS-SCIL-Consts where
-- in which we model constants of SCIL

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_+_ to _+'_)
open import Data.Product
open import Data.Nat.Properties
open import Data.Bool
open import Data.Sum

open import WS-Syn
open import WS-Exp

-- Types

Fcom  = F⊥ ◁ F⊤
Fbool = F⊥ ◁ (F⊤ ⊕ F⊤)
Fvar  = Fbool & (Fcom & Fcom)

-- Operations on Boolean Expressions

P⊕i : ∀ {A} {Γ} → Bool → ⊢ A , Γ → ⊢ A ⊕ A , Γ
P⊕i true  = P⊕₁
P⊕i false = P⊕₂

P&i : ∀ {M} {Γ} → (Bool → ⊢ M , Γ) → ⊢ M & M , Γ
P&i f = P& (f true) (f false)

constB : Bool → ⊢ Fbool , ε
constB m = P◁ $ P⊥+ $ P⊕i m $ P⊤

unaryB : (Bool → Bool) → ⊢ Fbool , Fbool ⊥' , ε
unaryB f = P◁ $ P⊥⅋ $ P⊥+ $ P⅋₂ $ P⊘ $ P⊤◁ $ P⊤- $ P◁ $ P&i $ λ m → P⊥+ $ P⊕i (f m) $ P⊤

notPrf = unaryB not

-- and, or, equality ...

-- Constants for Imperative Flow

seq : ∀ (P : Fml +) → ⊢ F⊥ ◁ P , Fcom ⊥' , (F⊥ ◁ P) ⊥' , ε
seq P = P◁ $ P⊥⅋ $ P⊥⅋ $ P⊥+ $ P⅋₁ $ P⅋₂ $ P⊘ $ P⊤◁ $ P⊤◁ $ P⊤- $ P◁ $ P◁
        $ P⊥⅋ $ P⊥+ $ P⅋₂ $ P⊘ $ P⊤◁ $ P⊤- $ P◁ $ aux $ sym $ idem⊥f P
   where aux : ∀ {Q} → Q ≡ (P ⊥') ⊥' → ⊢ P ⊥' , Q , ε
         aux refl = Pid

ifthen : ∀ (P : Fml +) → ⊢ ↑ P , Fbool ⊥' , ↑ P ⊥' , ↑ P ⊥' , ε
ifthen P = P◁ $ P⊥⅋ $ P⊥⅋ $ P⊥⅋ $ P⊥+ $ P⅋₁ $ P⅋₁ $ P⅋₂ $ P⊘ $ P⊤◁ $ P⊤◁ $ P⊤◁ $ P⊤- $ P◁ $ P◁ $ P◁ $
            P& (Pstr {Γ = F⊥ , P , ε} aux) (Pstr {Γ = F⊥ , P , F⊤ ⊘ (P ⊥') , ε} aux)
      where Pid' : ∀ {P : Fml +} → ⊢ P ⊥' , P , ε
            Pid' {P} =  subst (λ X → ⊢ P ⊥' , X , ε) (idem⊥f P) (Pid {P ⊥'})
            aux : ⊢ F⊥ , P , F⊤ ⊘ (P ⊥') , ε
            aux = P⊥⅋ $ P⊥+ $ P⅋₂ $ P⊘ $ P⊤◁ $ P⊤- $ P◁ $ Pid'

repeat : ∀ n → ⊢ Fcom , (! n Fcom) ⊥' , ε
repeat n = P◁ $ P⊥⅋ $ P⊥+ $ repeat' n
    where repeat' : ∀ n → ⊢ F⊤ ⅋ (! n (F⊥ ◁ F⊤) ⊥') , ε
          repeat' zero = P⅋₁ $ P⊤+ $ P⊤
          repeat' (suc n') = P⅋₂ $ P◁ $ P⊘ $ P⊤◁ $ P⊤◁ $ P⊤- $ P◁
                            $ P◁ $ Psym {Γ = F⊥ , ε} $ P⊥⅋ $ P⊥+ $ repeat' n'

-- Finitary Ground Store (of Booleans)

deref : ⊢ Fbool , Fvar ⊥' , ε
deref = P⊕T₁ {Γ = [ Fbool ]'} Pid 


assign : ⊢ Fcom , Fbool ⊥' , Fvar ⊥' , ε
assign = P⊕T₂ {Γ = Fcom , Fbool ⊥' , ε} $ P◁ $ P⊥⅋ $ P⊥⅋ $ P⊥+ $ P⅋₁ $ P⅋₂ $ P⊘ $ P⊤◁ $ P⊤◁ $ P⊤- $ P◁ $ P◁ $
         P&i $ λ m → P⊥⅋ $ P⊥+ $ P⅋₂ $ P⊕i m $ P⊘ $ P⊤◁ $ P⊤- $ P◁ $ P⊥+ $ P⊤

cell : ∀ n → Bool → ⊢ ! n Fvar , ε
cell zero    m = P1
cell (suc n) m = P⊘ $ P& (P◁ $ P⊥⊘ $ P⊥+ $ P⊘ $ P⊕i m $ P⊤- $ cell n m)
                         (P&i $ λ v → P◁ $ P⊥⊘ $ P⊥+ $ P⊘ $ P⊤- $ cell n v)


-- Coroutines

-- Coroutine Creators: We can take a coroutine k (!com -o com) and
-- wrap it in something of type (T -o !com), rooting the output move
-- of k to the move in T, and calls to the parameter of k to
-- temporarily leaving the coroutine.

Fcc : ℕ → Fml -
Fcc = λ n → Fcom ◁ ((! n Fcom) ⊥')

--                    1      2      3 (Fcom)   4 (! n Fcom ⊥')
createco : ∀ n → ⊢ ! n Fcom , F⊤ , (Fcc n) ⊥' , ε
createco zero    = P1
createco (suc n) = P⊘ $ P◁ $ P⊥⊘ $ P⊥⅋ $ P⊥⅋ $ P⊥+ $ -- O-move in 1
                   P⅋₂ $ P⊘ $ P⊘ $ P⊤⊗ $ P⊤◁ $ P⊤- $ P◁ $ -- P-move in 3
                   P⊗ (P⊥- $ P⊥+ $ P⅋₂ $ P⊤+ $ P⊤) -- O-move in 3, P-move in 2
                      (P⊘ $ P◁ $ P⊥⊘ $ P⊥⊘ $ P⊥⅋ $ P⊥+ $ -- O-move in 4
                       P⅋₂ $ P⅋₁ $ P⊘ $ P⊤◁ $ P⊤◁ $ P⊤- $ -- P-move in 1
                       P◁ $ P◁ $ Pcut {Γ = ! n (F⊥ ◁ F⊤) , F⊤ , ε} -- Recurse
                         ((F⊤ ⊘ ((! n (F⊥ ◁ F⊤) ⊥') ⊥')) ⊘ F⊥ , ε) (createco n) symprf)
           where Pid' : ∀ {P} {N} → ⊢ (P ⊥') ⊗ N , P ⅋ (N ⊥') , ε
                 Pid' {P} {N} rewrite sym $ cong (λ X → X ⅋ (N ⊥')) (idem⊥f P) = Pid {(P ⊥') ⊗ N}
                 symprf : ∀ {P} → ⊢ (F⊥ ◁ F⊤) ◁ P , (F⊤ ⊘ (P ⊥')) ⊘ F⊥ , ε
                 symprf {P} = P◁ $ P◁ $ P⊥⅋ $ P⊥⅋ $ P⊥+ $ P⅋₂ $ P⊘ $ P⊘ $ P⊤⊗ $ P⊤◁ $ P⊤-
                          $ P◁ $ P⅋T {Γ = (P ⊥') ⊗ F⊥ , ε} $ Psym {Γ = (P ⊥') ⊗ F⊥ , ε}
                               $ P⅋Tb {Γ = (P ⊥') ⊗ F⊥ , ε} $ Pid'

-- Composing two coroutines in parallel.

forget : ⊢ F⊥ ⊗ F⊥ , [ F⊤ ]
forget = P⊗ (P⊥- $ P⊥+ $ P⊤) (P⊥- $ P⊥+ $ P⊤)

Pid' : ∀ {N : Fml -} → ⊢ N ⊥' ⊥' , N ⊥' , ε
Pid' {N} rewrite idem⊥f N = Pid

cocomp : ∀ n → ⊢ Fcom , (Fcc n) ⊥' , (Fcc n) ⊥' , ε
cocomp n = Psym {Γ = [ Fcom ]'} $
            Pcut {Γ = F⊥ ◁ F⊤ , ε} {M = Fcom ◁ F⊤} (Fcc n ⊥' , Fcc n ⊥' , ε)
              (P◁ $ P⊥⅋ $ P⊥+ $ P⅋₂ $ P⊘ $ P⊘ $ P⊤⊗ $ P⊤◁ $ P⊤- $ P◁ $ forget)
                                    aux
   where aux : ⊢ Fcom ◁ F⊤ , (Fcc n) ⊥' , (Fcc n) ⊥' , ε
         aux = P◁ $ Pcut {Γ = [ Fcom ]'} (F⊤ , Fcc n ⊥' , ε)
            (Psym {Γ = F⊥ ◁ F⊤ , ε} $ P⊸ {F⊥ ◁ F⊤} {ε} (! n (F⊥ ◁ F⊤) ⊥' , ε) Pid Pid')
            (createco n)

-- Dealing with different values for the two occurences of n

Fccincr : ∀ n m → ⊢ Fcc (n +' m) , Fcc n ⊥' , ε
Fccincr n m = P◁ $ Psym {Γ = [ F⊥ ◁ F⊤ ]'} $
              P⊸ {M = Fcom} {Γ = ε} {P = Fcom ⊥'} (! (n +' m) (F⊥ ◁ F⊤) ⊥' , ε)
              Pid incr'
   where incr' : ⊢ (! n (F⊥ ◁ F⊤)) ⊥' ⊥' , ! (n +' m) (F⊥ ◁ F⊤) ⊥' , ε
         incr' rewrite idem⊥f (! n (F⊥ ◁ F⊤)) = !incr n m Fcom

cocomp1 : ∀ n m → ⊢ Fcom , (Fcc (n +' m)) ⊥' , (Fcc n) ⊥' , ε
cocomp1 n m = Pcut {Γ = Fcom , Fcc (n +' m) ⊥' , ε} {M = Fcc (n +' m)}
                (Fcc n ⊥' , ε) (cocomp (n +' m)) (Fccincr n m)
             
cocomp2 : ∀ n m → ⊢ Fcom , (Fcc n) ⊥' , (Fcc (n +' m)) ⊥' , ε
cocomp2 n m = Pcut {Γ₁ = [ Fcc (n +' m) ⊥' ]} {Γ = Fcom , ε}
                (Fcc n ⊥' , ε) (cocomp (n +' m)) (Fccincr n m)

lemma : ∀ n m → (Σ ℕ (λ k → n ≡ m +' k)) ⊎ (Σ ℕ (λ k → m ≡ n +' k))
lemma zero m = inj₂ $ m , refl
lemma (suc n) zero = inj₁ $ suc n , refl
lemma (suc n) (suc m) with lemma n m
lemma (suc n) (suc m) | inj₁ (k , eq) rewrite eq = inj₁ $ k , refl
lemma (suc n) (suc m) | inj₂ (k , eq) rewrite eq = inj₂ $ k , refl

cocompgen : ∀ n m → ⊢ Fcom , (Fcc n) ⊥' , (Fcc m) ⊥' , ε
cocompgen n m with lemma n m
cocompgen n m | inj₁ (_ , eq) rewrite eq = cocomp1 _ _
cocompgen n m | inj₂ (_ , eq) rewrite eq = cocomp2 _ _



