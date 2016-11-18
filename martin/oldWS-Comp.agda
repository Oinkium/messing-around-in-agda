{-# OPTIONS  --no-termination-check #-}

module WS-Comp where
-- in which we define a procedure turning strategies into core proofs
-- this yields the unique core proof with the same semantics as the
-- given strategy.

-- the no-termination-check is required since Agda is not convinced
-- that reify is terminating. It is, but the proof of this has yet to
-- be formalised in Agda.

open import Data.Function
open import Data.Sum as DS
open import Relation.Binary.PropositionalEquality

open import WS-Syn
open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import WS-Sem-Fsc

⟦≈1⟧+ : (Γ : Ctx) → ⟦ Γ ⟧+ I ≈ I
⟦≈1⟧+ ε               = id≈
⟦≈1⟧+ (_,_ { + } M Γ) = (⟦ Γ ⟧≈+ dist01) ≈∘≈ (⟦≈1⟧+ Γ)
⟦≈1⟧+ (_,_ { - } P Γ) = (⟦ Γ ⟧≈+ dist02) ≈∘≈ (⟦≈1⟧+ Γ)

un⟦P⊕⟧ : ∀{Γ P Q} → Strat + ⟦ P ⊕ Q , Γ ⟧'
          → Strat + ⟦ P , Γ ⟧' ⊎ Strat + ⟦ Q , Γ ⟧'
un⟦P⊕⟧ {Γ} {P} {Q} σ
   = DS.map (cast+' {P , ε} {Γ}) (cast+' {Q , ε} {Γ}) $
     coprod $ (cast+ {P ⊕ Q , ε} {Γ} σ) ∘≈ distΓ+ Γ

un⟦P⅋⟧ : ∀{Γ P Q} → Strat + ⟦ P ⅋ Q , Γ ⟧'
          → Strat + ⟦ P , Q , Γ ⟧' ⊎ Strat + ⟦ Q , P , Γ ⟧'
un⟦P⅋⟧ {Γ} {P} {Q} σ
   = DS.map (cast+' {P , Q , ε} {Γ}) (cast+' {Q , P , ε} {Γ}) $ coprod $
               cast+ {P ⅋ Q , ε} {Γ} σ ∘≈ ⟦ Γ ⟧≈+ dec1 ∘≈ distΓ+ Γ

un⟦P⊗1⟧ :  ∀ {Γ M N} → Strat - ⟦ M ⊗ N , Γ ⟧' → Strat - ⟦ M , N , Γ ⟧'
un⟦P⊗1⟧ {Γ} {M} {N} σ
  = cast-' {M , N , ε} {Γ} $ pi1 $ distΓ- Γ ≈∘ ⟦ Γ ⟧≈- dec1 ≈∘ cast- {M ⊗ N , ε} {Γ} σ

un⟦P⊗2⟧ :  ∀ {Γ M N} → Strat - ⟦ M ⊗ N , Γ ⟧' → Strat - ⟦ N , M , Γ ⟧'
un⟦P⊗2⟧ {Γ} {M} {N} σ
  = cast-' {N , M , ε} {Γ} $ pi2 $ distΓ- Γ ≈∘ ⟦ Γ ⟧≈- dec1 ≈∘ cast- {M ⊗ N , ε} {Γ} σ


un⟦P&1⟧ : ∀ {Γ M N} → Strat - ⟦ M & N , Γ ⟧' → Strat - ⟦ M , Γ ⟧'
un⟦P&1⟧ {Γ} {M} {N} σ = cast-' {M , ε} {Γ} $ pi1 $ distΓ- Γ ≈∘ cast- {M & N , ε} {Γ} σ


un⟦P&2⟧ : ∀ {Γ M N} → Strat - ⟦ M & N , Γ ⟧' → Strat - ⟦ N , Γ ⟧'
un⟦P&2⟧ {Γ} {M} {N} σ = cast-' {N , ε} {Γ} $ pi2 $ distΓ- Γ ≈∘ cast- {M & N , ε} {Γ} σ


un⟦P↑-⟧ : ∀ {Γ P N} → Strat - ⟦ ↑ P , N , Γ ⟧' → Strat - ⟦ ↑(P ⊘ N) , Γ ⟧'
un⟦P↑-⟧ {Γ} {P} {N} σ
  =  cast-' {↑(P ⊘ N), ε} {Γ} $ ⟦ Γ ⟧≈- lfe ≈∘ cast- {↑ P , N , ε} {Γ} σ

un⟦P↓+⟧ : ∀ {Γ N P} → Strat + ⟦ ↓ N , P , Γ ⟧' → Strat + ⟦ ↓(N ◁ P) , Γ ⟧'
un⟦P↓+⟧ {Γ} {N} {P} σ
  = cast+' {↓(N ◁ P) , ε} {Γ} $ cast+ { ↓ N , P , ε} {Γ} σ ∘≈ ⟦ Γ ⟧≈+ lfe

un⟦P↑+⟧ : ∀ {Γ P Q} → Strat - ⟦ ↑ P , Q , Γ ⟧' → Strat - ⟦ ↑(P ⅋ Q) , Γ ⟧'
un⟦P↑+⟧ {Γ} {P} {Q} σ
  = cast-' {↑(P ⅋ Q) , ε} {Γ} $ ⟦ Γ ⟧≈- curryo ≈∘ cast- {↑ P , Q , ε} {Γ} σ

un⟦P↓-⟧ : ∀ {Γ M N} → Strat + ⟦ ↓ M , N , Γ ⟧' → Strat + ⟦ ↓(M ⊗ N) , Γ ⟧'
un⟦P↓-⟧ {Γ} {M} {N} σ
  = cast+' {↓(M ⊗ N) , ε} {Γ} $ cast+ {↓ M , N , ε} {Γ} σ ∘≈ ⟦ Γ ⟧≈+ curryo


un⟦P↑⟧ : ∀ {P} → Strat - ⟦ ↑ P , ε ⟧' → Strat + ⟦ P , ε ⟧'
un⟦P↑⟧ σ = unσ⊸o σ

un⟦P↓⟧ : ∀ {N} → Strat + ⟦ ↓ N , ε ⟧' → Strat - ⟦ N , ε ⟧'
un⟦P↓⟧ σ = unσ⊸o σ

reify : ∀ {p}{Γ : Seq p} → Strat p ⟦ Γ ⟧' → ⊢ Γ
reify {.+ } {F0 , Γ} σ
  = f (subst (Strat +) (sym $ ⟦Δ⟧+⟦P⟧≡⟦P,Δ⟧ Γ) σ ∘≈ ⟦≈1⟧+ Γ)
  where f : Strat + I → ⊢ F0 , Γ
        f (pos () f)
reify {.- } {F1 , Γ} σ = P1
reify {.- } {↑ P , ε} σ = P↑ $ reify $ un⟦P↑⟧ {P} σ
reify {.- } {↑ P , (_,_ { + } Q Γ)} σ = P↑+ $ reify $ un⟦P↑+⟧ {Γ} σ
reify {.- } {↑ P , (_,_ { - } M Γ)} σ = P↑- $ reify $ un⟦P↑-⟧ {Γ} σ
reify {.+ } {↓ N , ε} σ = P↓ $ reify $ un⟦P↓⟧ {N} σ
reify {.+ } {↓ N , (_,_ { + } Q Γ)} σ = P↓+ $ reify $ un⟦P↓+⟧ {Γ} σ
reify {.+ } {↓ N , (_,_ { - } M Γ)} σ = P↓- $ reify $ un⟦P↓-⟧ {Γ} σ
reify {.- } {M ⊗ N , Γ} σ = P⊗ p₁ p₂
   where p₁ = reify { - } {M , N , Γ} $ un⟦P⊗1⟧ {Γ} {M} {N} σ
         p₂ = reify { - } {N , M , Γ} $ un⟦P⊗2⟧ {Γ} {M} {N} σ
reify {.+ } {P ⅋ Q , Γ} σ with un⟦P⅋⟧ {Γ} σ
...                         | inj₁ τ = P⅋₁ (reify {+} {P , Q , Γ} τ)
...                         | inj₂ τ = P⅋₂ (reify {+} {Q , P , Γ} τ)
reify {.+} {P ⊕ Q , Γ} σ with un⟦P⊕⟧ {Γ} σ
...                         | inj₁ τ = P⊕₁ (reify {+} {P , Γ} τ)
...                         | inj₂ τ = P⊕₂ (reify {+} {Q , Γ} τ)
reify {.- } {M & N , Γ} σ = P& p₁ p₂
   where p₁ = reify { - } {M , Γ} $ un⟦P&1⟧ {Γ} {M} {N} σ
         p₂ = reify { - } {N , Γ} $ un⟦P&2⟧ {Γ} {M} {N} σ
reify {p} {A ⊘ M , Γ} σ = P⊘ (reify {p} {A , M , Γ} σ)
reify {p} {A ◁ P , Γ} σ = P◁ (reify {p} {A , P , Γ} σ)

-- We can use reify for reduction-free normalisation of proofs to core
-- proofs:

open import WS-Sem

nbe : ∀ {p}{Γ : Seq p} → ⊢ Γ → ⊢ Γ
nbe p = reify ⟦ p ⟧⊢

data _<r_ : ∀ {p q} Seq p → Seq q → Set where
   p↑ : ∀ {P} → P , ε <r ↑ P , ε
   p↑+ : ∀ {P Q Γ} → ↑ (P ⅋ Q) , Γ <r ↑ P , Q , Γ 
   p↑- : ∀ {P N Γ} → ↑ (P ⊘ N) , Γ <r ↑ P , N , Γ
   p&₁ : ∀ {M N Γ} → M , Γ <r M & N , Γ
   p&₂ : ∀ {M N Γ} → N , Γ <r M & N , Γ
   p⊗₁ : ∀ {M N Γ} → M , N , Γ <r M ⊗ N , Γ
   p⊗₂ : ∀ {M N Γ} → N , M , Γ <r M ⊗ N , Γ
   p⊘ : ∀ {A M Γ} → A , M , Γ <r A ⊘ M , Γ
   p◁ : ∀ {A P Γ} → A , P , Γ <r A ◁ P , Γ
   p↓ : ∀ {N} → N , ε <r ↓ N  , ε
   p↓- : ∀ {M N Γ} → ↓ (M ⊗ N) , Γ <r ↓ M , N , Γ 
   p↓+ : ∀ {M P Γ} → ↓ (M ◁ P) , Γ <r ↓ M , P , Γ
   P⊕₁ : ∀ {P Q Γ} → P , Γ <r P ⊕ Q , Γ
   P⊕₂ : ∀ {P Q Γ} → Q , Γ <r P ⊕ Q , Γ
   P⅋₁ : ∀ {P Q Γ} → P , Q , Γ <r P ⅋ Q , Γ
   P⅋₂ : ∀ {P Q Γ} → Q , P , Γ <r P ⅋ Q , Γ



-- Termination of Reify
{-
open import Data.Nat
open import Data.Product renaming (_,_ to _,'_ ; ,_ to ,'_)

clength : Ctx → ℕ
clength ε       = zero
clength (_ , Γ) = suc (clength Γ)

flength : PolFml → ℕ
flength (._ ,' F0) = suc zero
flength (._ ,' F1) = suc zero
flength (._ ,' ↑ P) = suc $ flength $ ,' P
flength (._ ,' ↓ M) = suc $ flength $ ,' M
flength (._ ,' M ⊗ N) = suc $ _+_ (flength $ ,' M) (flength $ ,' N)
flength (._ ,' P ⅋ Q) = suc $ _+_ (flength $ ,' P) (flength $ ,' Q)
flength (._ ,' P ⊕ Q) = suc $ _+_ (flength $ ,' P) (flength $ ,' Q)
flength (._ ,' M & N) = suc $ _+_ (flength $ ,' M) (flength $ ,' N)
flength ( _ ,' A ⊘ M) = suc $ _+_ (flength $ ,' A) (flength $ ,' M)
flength ( _ ,' A ◁ P) = suc $ _+_ (flength $ ,' A) (flength $ ,' P)

clength' : Ctx → ℕ
clength' ε = zero
clength' (A , Γ) = _+_ (flength $ ,' A) (clength' Γ)

slength : PolSeq → ℕ
slength ( _ ,' (A , Γ)) = _+_ (flength $ ,' A) (clength' Γ)

import Induction.WellFounded as WF

head : PolSeq → PolFml
head ( _ ,' (A , Γ)) = ,' A

open import Relation.Binary.Core
_⟪_ = _<′_ on clength
_<₁_ = _<′_ on slength
_<₃_ = _<′_ on (flength ∘ head)

open WF _<′_ using (acc) renaming (Acc to <-Acc ; WfRec to <-WfRec)
open WF _⟪_  using (acc) renaming (Acc to ⟪-Acc ; WfRec to ⟪-WfRec)
open WF _<₁_ using (acc) renaming (Acc to <₁-Acc ; WfRec to <₁-WfRec)
open WF _<₃_ using (acc) renaming (Acc to <₃-Acc ; WfRec to <₃-WfRec)

⟪-lemAcc : ∀ {Γ} → <-Acc(clength Γ) → ⟪-Acc Γ
⟪-lemAcc (acc pΓ) = acc (λ Δ Δ⟪Γ → ⟪-lemAcc (pΓ (clength Δ) Δ⟪Γ))

<₁-lemAcc : ∀ {Γ} → <-Acc(slength Γ) → <₁-Acc Γ
<₁-lemAcc (acc pΓ) = acc (λ Δ Δ⟪Γ → <₁-lemAcc (pΓ (slength Δ) Δ⟪Γ))

<₃-lemAcc : ∀ {Γ} → <-Acc(flength $ head Γ) → <₃-Acc Γ
<₃-lemAcc (acc pΓ) = acc (λ Δ Δ⟪Γ → <₃-lemAcc (pΓ (flength $ head Δ) Δ⟪Γ))

open import Induction
open import Induction.Nat using (<-allAcc)

⟪-allAcc : ∀ Γ → ⟪-Acc Γ
⟪-allAcc Γ = ⟪-lemAcc (<-allAcc (clength Γ))

<₁-allAcc : ∀ Γ → <₁-Acc Γ
<₁-allAcc Γ = <₁-lemAcc (<-allAcc (slength Γ))

<₃-allAcc : ∀ Γ → <₃-Acc Γ
<₃-allAcc Γ = <₃-lemAcc (<-allAcc (flength $ head Γ))

infix 4 _<₂_

data _<₂_ : PolSeq → PolSeq → Set where
  only↑ : ∀ {A : Fml +} {p} {B : Fml p} {Γ} {Γ₁} → clength Γ <′ clength Γ₁
      → (- ,' ↑ A , Γ) <₂ (p ,' B , Γ₁)
  only↓ : ∀ {A : Fml - } {p} {B : Fml p} {Γ} {Γ₁} → clength Γ <′ clength Γ₁
      → (+ ,' ↓ A , Γ) <₂ (p ,' B , Γ₁)

open WF _<₂_ using () renaming (Acc to <₂-Acc ; WfRec to <₂-WfRec)

<₂-lemAcc : ∀ {p A Γ} → ⟪-Acc Γ → <₂-Acc (p ,' A , Γ)
<₂-lemAcc {p}{A}{Γ}(acc pΓ) = acc f
  where f : ∀ BΔ → BΔ <₂ (p ,' A , Γ) → <₂-Acc BΔ
        f ._ (only↑ {B} {.p} {.A} {Δ} Δ⟪Γ) = <₂-lemAcc (pΓ Δ Δ⟪Γ)
        f ._ (only↓ {B} {.p} {.A} {Δ} Δ⟪Γ) = <₂-lemAcc (pΓ Δ Δ⟪Γ)

<₂-allAcc : ∀ x → <₂-Acc x
<₂-allAcc (p ,' A , Γ) = <₂-lemAcc{p}{A} (⟪-allAcc Γ)

open WF.All _<₁_ <₁-allAcc public
  renaming ( wfRec-builder to <₁-rec-builder
           ; wfRec to <₁-rec
           )

open WF.All _<₂_ <₂-allAcc public
  renaming ( wfRec-builder to <₂-rec-builder
           ; wfRec to <₂-rec
           )

open WF.All _<₃_ <₃-allAcc public
  renaming ( wfRec-builder to <₃-rec-builder
           ; wfRec to <₃-rec
           )

open import Induction.Lexicographic renaming ([_⊗_] to [_⊗₁_] ; _⊗_ to _⊗₁_)

CombinedRecStruct = (<₁-WfRec ⊗₁ (<₂-WfRec ⊗₁ <₃-WfRec))
CombinedRecBuilder = [_⊗₁_]  <₁-rec-builder ([_⊗₁_] <₂-rec-builder <₃-rec-builder)

{-
FlatRecStruct : RecStruct PolSeq
FlatRecStruct P Γ = CombinedRecStruct
       (λ ppp → ((P $ proj₁ $ proj₁ ppp) × (P $ proj₂ $ proj₁ ppp)) × (P $ proj₂ ppp))
       (( Γ ,' Γ) ,' Γ)

FlatRecBuild : RecursorBuilder FlatRecStruct
FlatRecBuild P x x' = {!!} ,' {!CombinedRecBuilder!}
-}

--TypedStrat = Σ PolSeq (λ pΓ → Strat (proj₁ pΓ) ⟦ proj₂ pΓ ⟧')

--TS : RecStruct TypedStrat
--TS P (Γ ,' _) = CombinedRecStruct (λ ppp → {!!}) {!!}

-- CombinedRecStruct ?

--(((Γ ,' Γ) ,' Γ)) (λ ppp → P (,' σ))

-- build [ <₁-rec-builder ⊗ [ <₂-rec-builder ⊗ <₃-rec-builder] ] f

reify' : ∀ (pΓ : PolSeq) → Strat (proj₁ pΓ) ⟦ proj₂ pΓ ⟧' → ⊢ proj₂ pΓ
reify' pΓ σ = build
             CombinedRecBuilder
             reifypred reify'' ( pΓ ,' pΓ ,' pΓ) σ
   where reifypred : Σ (Σ Pol Seq) (λ _ → Σ (Σ Pol Seq) (λ _ → Σ Pol Seq)) → Set
         reifypred _ = Strat (proj₁ pΓ) ⟦ proj₂ pΓ ⟧' → ⊢ proj₂ pΓ
         reify'' : ∀ p → CombinedRecStruct reifypred p → reifypred p
         reify'' (pΓ₁ ,' pΓ₂ ,' pΓ₃) ((x ,' y) ,' y') σ' = {!pΓ₁!}

data _<<_ {A : Set0} {_<1_ _<2_ : A → A → Set} : A → A → Set where
    first : ∀ {x} {y} → x <1 y → x << y
    second : ∀ {x} {y} → x <2 y → x << y

module wfBack {A B : Set} (_<a_ : A → A → Set) (f : B → A) where
    open import Relation.Binary.Core
    import Induction.WellFounded as WF
    open WF _<a_ using (acc) renaming (Acc to <a-Acc ; WfRec to <a-WfRec)

    module All (allAccA : ∀ x → <a-Acc x) where

        _<b_ = _<a_ on f
        open WF _<b_ using (acc) renaming (Acc to <b-Acc ; WfRec to <b-WfRec)

        lemAcc : ∀ {b} → <a-Acc(f b) → <b-Acc b
        lemAcc (acc pΓ) = acc (λ Δ Δ⟪Γ → lemAcc (pΓ (f Δ) Δ⟪Γ))

        allAcc : ∀ b → <b-Acc b
        allAcc b = lemAcc (allAccA (f b))

module wfLexi {A B : Set} (_<a_ _=a_ : A → A → Set) (_<b_ : B → B → Set) where
   open import Data.Product
   data _<ab_ : A × B → A × B → Set where
       bya : ∀ {a1 a2 b1 b2} → a1 <a a2 → (a1 , b1) <ab (a2 , b2)
       byb : ∀ {a1 a2 b1 b2} → a1 =a a2 → b1 <b b2 → (a1 , b1) <ab (a2 , b2)
   
   import Induction.WellFounded as WF
   open WF _<a_ using (acc) renaming (Acc to <a-Acc ; WfRec to <a-WfRec)
   open WF _<b_ using (acc) renaming (Acc to <b-Acc ; WfRec to <b-WfRec)
   open WF _<ab_ using (acc) renaming (Acc to <ab-Acc ; WfRec to <ab-WfRec)

   module All (allAccA : ∀ x → <a-Acc x) (allAccB : ∀ x → <b-Acc x) where
   
-}
 
{-    open import Relation.Binary.Core
    _<b_ = _<a_ on f

    import Induction.WellFounded as WF
    open WF _<a_ using (acc) renaming (Acc to <a-Acc ; WfRec to <a-WfRec)
    open WF _<b_ using (acc) renaming (Acc to <b-Acc ; WfRec to <b-WfRec)

    module All (allAccA : ∀ x → <a-Acc x) where
        lemAcc : ∀ {b} → <a-Acc(f b) → <b-Acc b
        lemAcc (acc pΓ) = acc (λ Δ Δ⟪Γ → lemAcc (pΓ (f Δ) Δ⟪Γ))

        allAcc : ∀ b → <b-Acc b
        allAcc b = lemAcc (allAccA (f b))
 -}

--
{-
    ack : ∀ p → (N.Rec ⊗ N.Rec) AckPred p → AckPred p
    ack (zero  , n)     _                   = 1 + n
    ack (suc m , zero)  (_         , ackm•) = ackm• 1
    ack (suc m , suc n) (ack[1+m]n , ackm•) = ackm• ack[1+m]n
-}

--open WF _<₂_ { - } using (acc)

{-
allAcc : ∀ x → Acc x
allAcc (y , y') = acc (λ y₀ → f y₀)
   where f : (y₀ : Seq +) → y₀ <₂ y , y' → Acc y₀
         f .(↓ A , Γ) (only↓ {A} {.y} {Γ} y0) = {!!}
-}

{-
old:

postulate
  reifysound : ∀ {p} Γ → (σ : Strat p ⟦ Γ ⟧') → ⟦ reify {p} {Γ} σ ⟧⊢ x= σ
-}

