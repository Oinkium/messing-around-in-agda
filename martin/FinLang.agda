module FinLang where

open import Data.Nat
open import Data.List
open import Data.Product
open import Function
open import Data.Bool

-- Types of SCIL

infixr 5 _£_⇒_
infixr 5 _⊸_

data FLType : Set where
   Com ♭ool var : FLType
   _×'_   : FLType → FLType → FLType
   _£_⇒_ : FLType → ℕ → FLType → FLType

_⊸_ : FLType → FLType → FLType
_⊸_ = λ x y → _£_⇒_ x 1 y  

-- Constants

data FLConst : FLType → Set where
  ifB : FLConst (♭ool ⊸ ♭ool ⊸ ♭ool ⊸ ♭ool)
  ifC : FLConst (♭ool ⊸ Com ⊸ Com ⊸ Com)
  seqB : FLConst (Com ⊸ ♭ool ⊸ ♭ool)
  seqC : FLConst (Com ⊸ Com ⊸ Com)
  cor : ∀ n m → FLConst ((Com £ n ⇒ Com) ⊸ (Com £ m ⇒ Com) ⊸ Com)
  derf : FLConst (var ⊸ ♭ool)
  assgn : FLConst (var ⊸ ♭ool ⊸ Com)
  new : ∀ n A → Bool → FLConst ((var £ n ⇒ A) ⊸ A)
  nott : FLConst (♭ool ⊸ ♭ool)
  repeats : ∀ n → FLConst (Com £ n ⇒ Com)

-- Variables and Contexts

Var : Set
Var = ℕ

FLCtx : Set
FLCtx = List (Var × FLType × ℕ)

data compat : FLCtx → FLCtx → Set where
  κ : ∀ {Γ Γ'} v t m n → compat Γ Γ' → compat ((v , t , m) ∷ Γ) ((v , t , n) ∷ Γ')
  κ[] : compat [] []

comb : ∀ {Γ Γ'} → compat Γ Γ' → FLCtx
comb (κ v t m n y) = ( v , t , (m + n)) ∷ comb y
comb κ[] = []

mult : FLCtx → ℕ → FLCtx
mult [] m                 = []
mult ((x , t , n) ∷ xs) m = (x , t , n * m) ∷ mult xs m

cmlem : ∀ {a b} → compat a b → (n : ℕ) → compat (mult b n) a
cmlem (κ v t m n y) n' = κ v t (n * n') m (cmlem y n')
cmlem κ[] n' = κ[]

-- Lambda Calculus

data isin : Var → FLType → FLCtx → Set where
   intl : ∀ v Γ x t → isin v t Γ → isin v t (x ∷ Γ)
   inhd : ∀ v Γ t n → isin v t ((v , t , suc n) ∷ Γ)

data FLTerm : FLCtx → FLType → Set where
   konst : ∀ {t Γ} → FLConst t → FLTerm Γ t
   vart : ∀ {t Γ} → (v : Var) → isin v t Γ → FLTerm Γ t
   abs : ∀ {a b Γ n} → (v : Var) → FLTerm ((v , a , n) ∷ Γ) b → FLTerm Γ (a £ n ⇒ b)
   app : ∀ {a b Γ Δ n} → (c : compat Γ Δ) → FLTerm Γ (a £ n ⇒ b) → FLTerm Δ a
           → FLTerm (comb $ cmlem c n) b

-- Translation

open import WS-Syn
open import WS-Exp
open import WS-SCIL-Consts
open import Relation.Binary.PropositionalEquality

-- Translation of Types

toFml : FLType → Fml -
toFml Com  = Fcom
toFml ♭ool = Fbool
toFml var = Fvar
toFml (y ×' y') = toFml y & toFml y'
toFml (y £ y' ⇒ y0) = (toFml y0) ◁ ((! y' (toFml y)) ⊥')

toCtx : FLCtx → Ctx
toCtx [] = ε
toCtx ((_ , t , n) ∷ Γ) = (! n (toFml t)) ⊥' , toCtx Γ

ctx+ve : ∀ Γ → (ctxpol +) (toCtx Γ)
ctx+ve [] = ε
ctx+ve ((_ , t , n) ∷ xs) = ((! n (toFml t)) ⊥') , ctx+ve xs

-- Translation of Constants

add◁F0 : ∀ {p} {Γ : Seq p} {P : Fml +} {Δ}
               → ⊢ Γ ,,₀ (P , Δ) → ⊢ Γ ,,₀ (P ◁ F0 , Δ)
add◁F0 {p} {Γ} {P} {Δ} prf rewrite sym $ ,,₀assoc Γ {P ◁ F0 , ε} {Δ} = aux prf
  where aux₁ : ⊢ P ⊥' , P ◁ F0 , ε
        aux₁ = P1Tb {Γ = [ P ⊥' ]'} $
             subst (λ F → ⊢ P ⊥' , F1 , F ◁ F0 , ε) (idem⊥f P) (Pid⊘ ε P1)
        aux : ⊢ Γ ,,₀ (P , Δ) → ⊢ Γ ,,₀ (P ◁ F0 , ε) ,,₀ Δ
        aux prf = Pcut {Γ₁ = Δ} {Γ = Γ} {M = P ⊥'} (P ◁ F0 , ε)
             (subst (λ F → ⊢ Γ ,,₀ (F , Δ)) (sym $ idem⊥f P) prf)
             aux₁

kToTrm : ∀ {T} → FLConst T → ⊢ toFml T , ε
kToTrm ifB = P◁ $ P◁ $ P◁
          $ add◁F0 {Γ = [ Fbool ]'}
          $ add◁F0 {Γ = Fbool , Fbool ⊥' , ε}
          $ add◁F0 {Γ = Fbool , Fbool ⊥' , Fbool ⊥' , ε}
          $ Psym {Γ = Fbool , Fbool ⊥' , ε}
          $ Psym {Γ = Fbool , ε}
          $ ifthen (F⊤ ⊕ F⊤)
kToTrm ifC = P◁ $ P◁ $ P◁
          $ add◁F0 {Γ = [ Fcom ]'}
          $ add◁F0 {Γ = Fcom , Fcom ⊥' , ε}
          $ add◁F0 {Γ = Fcom , Fcom ⊥' , Fcom ⊥' , ε}
          $ Psym {Γ = Fcom , Fcom ⊥' , ε}
          $ Psym {Γ = [ Fcom ]'}
          $ ifthen F⊤
kToTrm seqB = P◁ $ P◁ $ add◁F0 {Γ = [ Fbool ]'}  $
              add◁F0 {Γ = Fbool , Fbool ⊥' , ε} $ Psym {Γ = [ Fbool ]'} $
              seq (F⊤ ⊕ F⊤)
kToTrm seqC = P◁ $ P◁ $ add◁F0 {Γ = [ Fcom ]'} $
              add◁F0 {Γ = Fcom , Fcom ⊥' , ε} $ Psym {Γ = [ Fcom ]'} $
              seq F⊤
kToTrm (cor n m) = P◁ $ P◁ $ add◁F0 {Γ = [ Fcom ]'} $
                   add◁F0 {Γ = Fcom , Fcc m ⊥' , ε} $ cocompgen m n
kToTrm derf = P◁ $ add◁F0 {Γ = [ Fbool ]'} $ deref
kToTrm assgn = P◁ $ P◁ $ add◁F0 {Γ = [ Fcom ]'} $ add◁F0 {Γ = Fcom , Fbool ⊥' , ε} $ assign
kToTrm (new n A b) = P◁ $ add◁F0 {Γ = [ toFml A ]'} $
                     Pcut {Γ = toFml A , (toFml A ⊥') ⊘ ((! n Fvar ⊥') ⊥') , ε} ε
                       (P⊸ {toFml A} {ε} {toFml A ⊥'}
                          {(! n ((F⊥ ◁ (F⊤ ⊕ F⊤)) & ((F⊥ ◁ F⊤) & (F⊥ ◁ F⊤))) ⊥') ⊥'}
                          (! n ((F⊥ ◁ (F⊤ ⊕ F⊤)) & ((F⊥ ◁ F⊤) & (F⊥ ◁ F⊤))) ⊥' , ε) Pid Pid')
                       (cell n b)
kToTrm nott = P◁ $ add◁F0 {Γ = [ Fbool ]'} $ notPrf
kToTrm (repeats n) = P◁ $ repeat n

-- Translation of Lambda Calculus

weak : ∀ {Δ p} (M : Fml p) → (ctxpol +) Δ → ⊢ M , ε → ⊢ M , Δ
weak M ε prf = prf
weak M (P , y) prf = Pstr {Γ = [ M ]'} $ weak M y prf


promo : ∀ {Γ} {M : Fml - } n → ⊢ M , toCtx Γ → ⊢ ! n M , toCtx (mult Γ n)
promo {[]} {M} n prf = P0Tb {Γ = [ ! n M ]'} $
                        Pcut {Γ = [ ! n M ]'} (F0 , ε)
                         (prom n M F1 $ P0T {Γ = [ M ]'} $ prf)
                         (bang0 n)
promo {(v , t , m) ∷ xs} {M} n prf rewrite sym $ ,,ε (! (m * n) (toFml t) ⊥' , toCtx (mult xs n))
   = Pcut {Γ₁ = ε} {Γ = ! n M , ! (m * n) (toFml t) ⊥' , ε} (ctx+ve $ mult xs n)
      (Pcut {Γ = [ ! n M ]'} (! (m * n) (toFml t) ⊥' , ε)
        (Pcut {Γ = [ ! n M ]'} ((! n (! m (toFml t)) ⊥') , (! n (M ◁ (! m (toFml t) ⊥')) ⊥') , ε)
           (prom n M (! m (toFml t) ⊗ (M ◁ (! m (toFml t) ⊥')))
           (P⅋T {Γ = [ M ]'} $ Psym {Γ = M , ε} $ (P⊸ {M} {ε} {M ⊥'}
                          {((! m (toFml t) ⊥') ⊥')} (! m (toFml t) ⊥' , ε) Pid Pid')))
         (!monoidal n (! m (toFml t)) (M ◁ (! m (toFml t) ⊥')) ))
        (!mult' n m (toFml t)))
      (promo {xs} n (P◁ prf))

symΔ : ∀ {p} { Γ : Seq p} {P : Fml +} {Δ₂} {Δ}  → (ctxpol +) Δ →
        ⊢ Γ ,,₀ (Δ ,, (P , Δ₂)) → ⊢ Γ ,,₀ (P , Δ ,, Δ₂)
symΔ {p} {Γ} {P} {Δ₂} {ε} Δ' prf      = prf
symΔ {p} {Γ} {P} {Δ₂} {Q , Δ₁} (.Q , y) prf = Psym {Γ = Γ} $ aux
     where aux₁ : ⊢ Γ ,,₀ (Q , ε) ,,₀ (Δ₁ ,, (P , Δ₂))
           aux₁ rewrite ,,₀assoc Γ {Q , ε} {Δ₁ ,, (P , Δ₂)} = prf
           aux : ⊢ Γ ,,₀ (Q , P , Δ₁ ,, Δ₂)
           aux rewrite sym $ ,,₀assoc Γ {Q , ε} {P , Δ₁ ,, Δ₂}
                      = symΔ {p} {Γ ,,₀ (Q , ε)} {P} {Δ₂} {Δ₁} y aux₁

combp : ∀ {Γ} {Γ'} {A : Seq - } (r : compat Γ Γ')
     → ⊢ A ,,₀ toCtx Γ ,, toCtx Γ' → ⊢ A ,,₀ toCtx (comb r)
combp {.((v , t , m) ∷ Γ)} {.((v , t , n) ∷ Γ')} {A} (κ {Γ} {Γ'} v t m n y) prf
     rewrite sym $ ,,₀assoc A { ! (_+_ m n) (toFml t) ⊥' , ε} {toCtx (comb y)}
     = Pcut {Γ = A} (! (_+_ m n) (toFml t) ⊥' , ε) (P⅋T {Γ = A} $ aux) (contr m n (toFml t))
     where prf₁ : ⊢ (A ,,₀ (! m (toFml t) ⊥' , ε)) ,,₀ (toCtx Γ  ,, (! n (toFml t) ⊥' , toCtx Γ'))
           prf₁ rewrite ,,₀assoc A {(! m (toFml t) ⊥') , ε} {(toCtx Γ ,, (! n (toFml t) ⊥' , toCtx Γ'))} = prf
           id₁ : ⊢ A ,,₀ (! m (toFml t) ⊥' , ε) ,,₀ (! n (toFml t) ⊥' , toCtx Γ ,, toCtx Γ') →
               ⊢ (A ,,₀ (! m (toFml t) ⊥' , ε) ,,₀ (! n (toFml t) ⊥' , ε)) ,,₀ toCtx Γ ,, toCtx Γ'
           id₁ pr rewrite ,,₀assoc (A ,,₀ (! m (toFml t) ⊥' , ε)) { ! n (toFml t) ⊥' , ε} {toCtx Γ ,, toCtx Γ'} = pr
           combp_y : ⊢ A ,,₀ (! m (toFml t) ⊥' , ε) ,,₀ (! n (toFml t) ⊥' , toCtx Γ ,, toCtx Γ') →
                  ⊢ A ,,₀ (! m (toFml t) ⊥' , ! n (toFml t) ⊥' , toCtx (comb y))
           combp_y pr rewrite sym $ ,,₀assoc A { ! m (toFml t) ⊥' , ! n (toFml t) ⊥' , ε} {toCtx (comb y)} |
                        cong (λ R → ⊢ R ,,₀ toCtx (comb y)) (sym $ ,,₀assoc A { ! m (toFml t) ⊥' , ε} { ! n (toFml t) ⊥' , ε})
                        = combp y (id₁ pr)
           aux : ⊢ A ,,₀ (! m (toFml t) ⊥' , (! n (toFml t) ⊥' , toCtx (comb y)))
           aux = combp_y $ symΔ { - } {A ,,₀ ((! m (toFml t) ⊥') , ε)} { ! n (toFml t) ⊥'} {toCtx Γ'} {toCtx Γ} (ctx+ve Γ) prf₁
combp {.[]} {.[]} {A} κ[] prf = prf


Pid'' : ∀ {P : Fml +} → ⊢ P ⊥' , P , ε
Pid'' {P} rewrite cong (λ R → ⊢ P ⊥' , R , ε) (sym $ idem⊥f P) = Pid

P◁b : ∀ {P Δ} {N : Fml -} → (ctxpol +) Δ → ⊢ N ◁ P , Δ → ⊢ N , P , Δ
P◁b {P} {Δ} {N} Δ₁ prf rewrite cong (λ R → ⊢ N , P , R) (sym $ ,,ε Δ) = Pcut {Γ = N , P , ε} {M = N ◁ P} Δ₁ p₁ prf
   where p₁ : ⊢ N , P , (N ◁ P) ⊥' , ε
         p₁ = Psym {Γ = [ N ]'} $ P⊸ {N} {ε} {N ⊥'} {P ⊥'} {P , ε} (P , ε) Pid Pid''

tToPrf : ∀ {T} {Γ} → FLTerm Γ T → ⊢ toFml T , toCtx Γ
tToPrf {T} {Γ} (konst y) = weak (toFml T) (ctx+ve Γ) (kToTrm y)
tToPrf {T} {.((x , x' , y) ∷ Γ)} (vart v (intl .v Γ (x , x' , y) .T y')) =
          Pstr {Γ = [ toFml T ]'} $ tToPrf {T} {Γ} (vart v y')
tToPrf {T} {.((v , T , suc n) ∷ Γ)} (vart v (inhd .v Γ .T n)) = 
          P◁b (ctx+ve Γ) $ weak (toFml T ◁ ((toFml T ⊥') ◁ (! n (toFml T) ⊥'))) (ctx+ve Γ) $
          P◁ $ Pcut {Γ = [ toFml T ]'} (! (suc n) (toFml T) ⊥' , ε)
              (P⅋T {Γ = [ toFml T ]'} $ add◁F0 {Γ = [ toFml T ]'} $
                Pstr {Γ = toFml T , toFml T ⊥' , ε} $ Pid)
              (contr 1 n (toFml T))
tToPrf {.(a £ n ⇒ b)} {Γ} (abs {a} {b} {.Γ} {n} v y) = P◁ $ tToPrf y
tToPrf {T} {.(comb (cmlem c n))} (app {a} {.T} {Γ} {Δ} {n} c y y')
    = combp {A = [ toFml T ]'} (cmlem c n) (Pcut {Γ = [ toFml T ]'} (ctx+ve $ mult Δ n)
             (P◁b (ctx+ve Γ) $ tToPrf y)
             (promo n $ tToPrf y')) 

-- Translation to Core Proofs

open import WS-Comp

tToCorePrf : ∀ {T} {Γ} → FLTerm Γ T → ⊢ toFml T , toCtx Γ
tToCorePrf t = nbe $ tToPrf t

-- Game Semantics of FinLang

open import WS-Sem
open import Game

⟦_⟧σ : ∀ {Γ} {T} → FLTerm Γ T → Strat - ⟦ toFml T , toCtx Γ ⟧'
⟦ t ⟧σ = ⟦ tToPrf t ⟧⊢