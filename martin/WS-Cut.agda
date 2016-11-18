{-# OPTIONS  --no-termination-check #-}

module WS-Cut where
-- in which we formalise the cut elimination procedure in WS

-- currently Agda doesn't see this as terminating
-- (limitation of termination checker?)

open import Data.Bool renaming (true to - ; false to +; Bool to Pol; not to ¬)
open import Data.Product renaming (,_ to `_)
open import Function
open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import WS-Syn renaming (P1 to P1' ; P⊗ to P⊗' ; P⅋₁ to P⅋₁' ; P⅋₂ to P⅋₂' ;
                             P⊕₁ to P⊕₁' ; P⊕₂ to P⊕₂' ; P& to P&' ; P⊥+ to P⊥+' ;
                             P⊥- to P⊥-' ; P⊥⊘ to P⊥⊘' ; P⊥⅋ to P⊥⅋'; P⊤ to P⊤' ;
                             P⊤+ to P⊤+' ; P⊤- to P⊤-' ; P⊤⊗ to P⊤⊗'; P⊤◁ to P⊤◁' ;
                             P⊘ to P⊘' ; P◁ to P◁')

-- Core rules of WS

infix 3 ⊢c_
data ⊢c_ : ∀ {p} → Seq p → Set where
  P1  : ∀ {Γ} → ⊢c F1 , Γ
  P⊗  : ∀ {M N Γ} → ⊢c M , N , Γ → ⊢c N , M , Γ → ⊢c M ⊗ N , Γ
  P⅋₁ : ∀ {P Q Γ} → ⊢c P , Q , Γ → ⊢c P ⅋ Q , Γ
  P⅋₂ : ∀ {P Q Γ} → ⊢c Q , P , Γ → ⊢c P ⅋ Q , Γ
  P⊕₁ : ∀ {P Q Γ} → ⊢c P , Γ → ⊢c P ⊕ Q , Γ
  P⊕₂ : ∀ {P Q Γ} → ⊢c Q , Γ → ⊢c P ⊕ Q , Γ
  P⊕ω : ∀ {P Γ}   → ℕ → ⊢c P , Γ → ⊢c ω⊕ P , Γ 
  P&  : ∀ {M N Γ} → ⊢c M , Γ → ⊢c N , Γ → ⊢c M & N , Γ
  P&ω : ∀ {M Γ}   → (ℕ → ⊢c M , Γ) → ⊢c ω& M , Γ
  P⊥+ : ∀ {P : Fml +} → ⊢c P , ε → ⊢c F⊥ , P , ε
  P⊥- : ∀ {N : Fml -} {Γ} → ⊢c F⊥ , Γ → ⊢c F⊥ , N , Γ 
  P⊥⊘ : ∀ {P : Fml +} {N Γ} → ⊢c F⊥ , P ⊘ N , Γ → ⊢c F⊥ , P , N , Γ
  P⊥⅋ : ∀ {P Q Γ} → ⊢c F⊥ , P ⅋ Q , Γ → ⊢c F⊥ , P , Q , Γ
  P⊤+ : ∀ {P : Fml +} {Γ} → ⊢c F⊤ , Γ → ⊢c F⊤ , P , Γ 
  P⊤  : ⊢c F⊤ , ε
  P⊤- : ∀ {N : Fml -} → ⊢c N , ε → ⊢c F⊤ , N , ε
  P⊤◁ : ∀ {N : Fml -} {P Γ} → ⊢c F⊤ , N ◁ P , Γ → ⊢c F⊤ , N , P , Γ
  P⊤⊗ : ∀ {M N Γ} → ⊢c F⊤ , M ⊗ N , Γ → ⊢c F⊤ , M , N , Γ
  P⊘  : ∀ {p}{A : Fml p}{M Γ} → ⊢c A , M , Γ → ⊢c A ⊘ M , Γ
  P◁  : ∀ {p}{A : Fml p}{P Γ} → ⊢c A , P , Γ → ⊢c A ◁ P , Γ

-- A lemma, needed for cut elimination to work

_↑F : Seq + → Fml +
(P , ε) ↑F = P
(P , (_,_ { - } M Γ)) ↑F = (P ⊘ M , Γ) ↑F
(P , (_,_ { + } Q Γ)) ↑F = (P ⅋ Q , Γ) ↑F

_↓F : Seq - → Fml -
(N , ε) ↓F = N
(N , (_,_ { - } M Γ)) ↓F = (N ⊗ M , Γ) ↓F
(N , (_,_ { + } Q Γ)) ↓F = (N ◁ Q , Γ) ↓F

_⊥c : Ctx → Ctx
ε ⊥c = ε
(y , y') ⊥c = y ⊥' , y' ⊥c

_⊥s : ∀ {p} → Seq p → Seq (¬ p)
(y , y') ⊥s = y ⊥' , y' ⊥c

idem⊥F : ∀ {Γ} → Γ ↑F ≡ Γ ⊥s ↓F ⊥'
idem⊥F {P , ε} = sym (idem⊥f P)
idem⊥F {P , (_,_ { - } N Γ)} with (P ⊘ N , Γ) ⊥s ↓F ⊥' | idem⊥F {P ⊘ N , Γ}
...                                | .((P ⊘ N , Γ) ↑F) | refl = refl
idem⊥F {P , (_,_ { + } Q Γ)} with (P ⅋ Q , Γ) ⊥s ↓F ⊥' | idem⊥F {P ⅋ Q , Γ}
...                                | .((P ⅋ Q , Γ) ↑F) | refl = refl

-- Weakening

wk : ∀ {p}{A : Fml p}{Γ}{P : Fml +} → ⊢c A , Γ → ⊢c A , Γ ,, (P , ε)
wk P1 = P1
wk P⊤ = P⊤+ P⊤
wk (P⊗ y y') = P⊗ (wk y) (wk y')
wk (P⅋₁ y) = P⅋₁ (wk y)
wk (P⅋₂ y) = P⅋₂ (wk y)
wk (P⊕₁ y) = P⊕₁ (wk y)
wk (P⊕₂ y) = P⊕₂ (wk y)
wk (P⊕ω y y') = P⊕ω y (wk y')
wk (P& y y') = P& (wk y) (wk y')
wk (P&ω y) = P&ω (λ n → wk (y n))
wk (P⊥+ y) = P⊥⅋ (P⊥+ (P⅋₁ (wk y)))
wk (P⊥- y) = P⊥- (wk y)
wk (P⊥⊘ y) = P⊥⊘ (wk y)
wk (P⊥⅋ y) = P⊥⅋ (wk y)
wk (P⊤+ y) = P⊤+ (wk y)
wk (P⊤- y) = P⊤◁ (P⊤- (P◁ (wk y)))
wk (P⊤◁ y) = P⊤◁ (wk y)
wk (P⊤⊗ y) = P⊤⊗ (wk y)
wk (P⊘ y) = P⊘ (wk y)
wk (P◁ y) = P◁ (wk y)


-- Cut Elimination (where Δ = P and Γ₁ = ε)

symP⅋ : ∀ {Γ P Q} → ⊢c P ⅋ Q , Γ → ⊢c Q ⅋ P , Γ
symP⅋ (P⅋₁ y) = P⅋₂ y
symP⅋ (P⅋₂ y) = P⅋₁ y

rem0 : ∀ {p}{Γ : Seq p} → ⊢c Γ ,,₀ (F0 , ε) → ⊢c Γ
rem0 {.+} {F0 , y'} ()
rem0 {.-} {F1 , y'} P1 = P1
rem0 {.-} {F⊥ , ε} (P⊥+ ())
rem0 {.-} {F⊥ , _,_ { - } A y'} (P⊥- prf) = P⊥- (rem0 prf)
rem0 {.-} {F⊥ , _,_ {+} A ε} (P⊥⅋ (P⊥+ (P⅋₁ prf))) = P⊥+ (rem0 prf)
rem0 {.-} {F⊥ , _,_ {+} A ε} (P⊥⅋ (P⊥+ (P⅋₂ ())))
rem0 {.-} {F⊥ , _,_ {+} A (_,_ { - } B y')} (P⊥⊘ prf) = P⊥⊘ (rem0 prf)
rem0 {.-} {F⊥ , _,_ {+} A (_,_ { + } B y')} (P⊥⅋ prf) = P⊥⅋ (rem0 prf)
rem0 {.+} {F⊤ , ε} (P⊤+ P⊤) = P⊤
rem0 {.+} {F⊤ , _,_ { -} A ε} (P⊤◁ (P⊤- (P◁ prf))) = P⊤- (rem0 prf)
rem0 {.+} {F⊤ , _,_ { -} A (_,_ { -} B y')} (P⊤⊗ prf) = P⊤⊗ (rem0 prf)
rem0 {.+} {F⊤ , _,_ { -} A (_,_ {+} B y')} (P⊤◁ prf) = P⊤◁ (rem0 prf)
rem0 {.+} {F⊤ , _,_ {+} A y'} (P⊤+ prf) = P⊤+ (rem0 prf)
rem0 {.-} {M ⊗ N , y'} (P⊗ prf prf') = P⊗ (rem0 prf) (rem0 prf')
rem0 {.+} {P ⅋ Q , y'} (P⅋₁ prf) = P⅋₁ (rem0 prf)
rem0 {.+} {P ⅋ Q , y'} (P⅋₂ prf) = P⅋₂ (rem0 prf)
rem0 {.+} {P ⊕ Q , y'} (P⊕₁ prf) = P⊕₁ (rem0 prf)
rem0 {.+} {P ⊕ Q , y'} (P⊕₂ prf) = P⊕₂ (rem0 prf)
rem0 {.-} {M & N , y'} (P& prf prf') = P& (rem0 prf) (rem0 prf')
rem0 {p} {A ⊘ M , y'} (P⊘ prf) = P⊘ (rem0 prf)
rem0 {p} {A ◁ P , y'} (P◁ prf) = P◁ (rem0 prf)
rem0 {.-} {ω& M , y'} (P&ω f) = P&ω (λ m → rem0 (f m))
rem0 {.+} {ω⊕ P , y'} (P⊕ω y y0) = P⊕ω y (rem0 y0)

un⅋0 : ∀ {P} → ⊢c F0 ⅋ P , ε → ⊢c P , ε
un⅋0 (P⅋₁ ())
un⅋0 (P⅋₂ prf) = rem0 prf

mutual
  cut : ∀ {p}{A : Fml p}(Γ : Ctx){N : Fml - }{P : Fml +} →
      ⊢c A , Γ ,, (N ⊥' , ε) → ⊢c N , P , ε → ⊢c A , Γ ,, (P , ε)
  cut {.+} {F0} Γ () g
  cut {.- } {F1} Γ h g = P1
  cut {.- } {F⊥} ε {N} (P⊥+ y) g = P⊥+ $ un⅋0 $ cut₂ (N , ε) (wk {P = F0} y) g
  cut {.- } {F⊥} (_,_ { - } N Γ') (P⊥- y) g             = P⊥- (cut Γ' y g)
  cut {.- } {F⊥} (_,_ { + } Q ε) (P⊥⅋ (P⊥+ (P⅋₁ y))) g = P⊥⅋ $ P⊥+ $ P⅋₁ (cut ε y g)
  cut {.- } {F⊥} (_,_ { + } Q ε) {N} (P⊥⅋ (P⊥+ (P⅋₂ y))) g = P⊥⅋ $ P⊥+ $ cut₂ (N , ε) y g
  cut {.- } {F⊥} (_,_ { + } Q (_,_ { + } P Γ')) (P⊥⅋ y) g = P⊥⅋ (cut (Q ⅋ P , Γ') y g)
  cut {.- } {F⊥} (_,_ { + } Q (_,_ { - } M Γ')) (P⊥⊘ y) g = P⊥⊘ (cut (Q ⊘ M , Γ') y g)
  cut {.+ } {F⊤} ε (P⊤+(P⊤)) g = P⊤+ $ P⊤
  cut {.+ } {F⊤} (_,_ { + } P Γ') (P⊤+ y) g = P⊤+ $ cut Γ' y g
  cut {.+ } {F⊤} (_,_ { - } M ε) (P⊤◁ (P⊤- (P◁ y))) g = P⊤◁ $ P⊤- $ P◁ $ cut ε y g
  cut {.+ } {F⊤} (_,_ { - } M (_,_ { + } P Γ')) (P⊤◁ y) g = P⊤◁ (cut (M ◁ P , Γ') y g)
  cut {.+ } {F⊤} (_,_ { - } M (_,_ { - } N Γ')) (P⊤⊗ y) g = P⊤⊗ (cut (M ⊗ N , Γ') y g)
  cut {.- } {y ⊗ y'} Γ (P⊗ y0 y1) g
    = P⊗ (cut (y' , Γ) y0 g) (cut (y , Γ) y1 g)
  cut {.+} {y ⅋ y'}  Γ (P⅋₁ y0) g   = P⅋₁ (cut (y' , Γ) y0 g)
  cut {.+} {y ⅋ y'}  Γ (P⅋₂ y0) g   = P⅋₂ (cut (y , Γ) y0 g)
  cut {p} {y ⊘ y'}   Γ (P⊘ y0) g    = P⊘  (cut (y' , Γ) y0 g)
  cut {p} {y ◁ y'}   Γ (P◁ y0) g    = P◁  (cut (y' , Γ) y0 g)
  cut {.+} {y ⊕ y'}  Γ (P⊕₁ y0) g   = P⊕₁ (cut Γ y0 g)
  cut {.+} {y ⊕ y'}  Γ (P⊕₂ y0) g   = P⊕₂ (cut Γ y0 g)
  cut {.+ } {ω⊕ f} Γ (P⊕ω n g) h = P⊕ω n (cut Γ g h)
  cut {.- } {y & y'} Γ (P& y0 y1) g = P&  (cut Γ y0 g) (cut Γ y1 g)
  cut {.- } {ω& f} Γ (P&ω g) h = P&ω (λ x → cut Γ (g x) h)

  cut₂ : ∀ (Γ : Seq -){Q R : Fml + } →
           ⊢c Γ ⊥s ,,₀ (Q , ε) → ⊢c Γ ,,₀ (R , ε) → ⊢c Q ⅋ R , ε
  cut₂ (F1 , y') () g
  cut₂ (F⊥ , ε) (P⊤+ P⊤) (P⊥+ y) = P⅋₂ $ wk y
  cut₂ (F⊥ , (_,_ { - } N Γ')) (P⊤+ y) (P⊥- y') = cut₂ (_ , Γ') y y'
  cut₂ (F⊥ , _,_ {+} P ε) {Q} {R} (P⊤◁ (P⊤- (P◁ y))) (P⊥⅋ (P⊥+ (P⅋₁ y'))) = symP⅋ $ cut₂ (P ⊥' , ε) y'₁ y
       where y'₁ = subst (λ X → ⊢c X , R , ε) (idem⊥F {P , ε})  y'
  cut₂ (F⊥ , _,_ {+} P ε) {Q} {R} (P⊤◁ (P⊤- (P◁ y))) (P⊥⅋ (P⊥+ (P⅋₂ y'))) = P⅋₂ $ cut ε y'₁ y
       where y'₁ = subst (λ X → ⊢c R , X , ε) (idem⊥F {P , ε}) y'
  cut₂ (F⊥ , (_,_ { + } P (_,_ { + } Q Γ'))) (P⊤⊗ y) (P⊥⅋ y') = cut₂ (F⊥ , P ⅋ Q , Γ') y y'
  cut₂ (F⊥ , (_,_ { + } P (_,_ { - } M Γ'))) (P⊤◁ y) (P⊥⊘ y') = cut₂ (F⊥ , P ⊘ M , Γ') y y'
  cut₂ (y ⊗ y' , y0) (P⅋₁ y1) (P⊗ y2 y3) = cut₂ (y , y' , y0) y1 y2
  cut₂ (y ⊗ y' , y0) (P⅋₂ y1) (P⊗ y2 y3) = cut₂ (y' , y , y0) y1 y3
  cut₂ (y ⊘ y' , y0) (P◁  y1) (P⊘ y2   ) = cut₂ (y , y' , y0) y1 y2
  cut₂ (y ◁ y' , y0) (P⊘  y1) (P◁ y2   ) = cut₂ (y , y' , y0) y1 y2
  cut₂ (y & y' , y0) (P⊕₁ y1) (P& y2 y3) = cut₂ (y , y0) y1 y2
  cut₂ (y & y' , y0) (P⊕₂ y1) (P& y2 y3) = cut₂ (y' , y0) y1 y3
  cut₂ (ω& y' , y0) (P⊕ω n y1) (P&ω y2) = cut₂ (y' , y0) y1 (y2 n)

