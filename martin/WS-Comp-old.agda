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

open import Data.Nat
open import Data.Product renaming (_,_ to _,'_)

clength : Ctx → ℕ
clength ε       = zero
clength (_ , Γ) = suc (clength Γ)

flength : ∀ {p} → Fml p → ℕ
flength F0 = suc zero
flength F1 = suc zero
flength (↑ P) = suc (flength P)
flength (↓ M) = suc (flength M)
flength (M ⊗ N) = suc (_+_ (flength M) (flength N))
flength (P ⅋ Q) = suc (_+_ (flength P) (flength Q))
flength (P ⊕ Q) = suc (_+_ (flength P) (flength Q))
flength (M & N) = suc (_+_ (flength M) (flength N))
flength (A ⊘ M) = suc (_+_ (flength A) (flength M))
flength (A ◁ P) = suc (_+_ (flength A) (flength P))

clength' : Ctx → ℕ
clength' ε = zero
clength' (A , Γ) = _+_ (flength A) (clength' Γ)

slength : ∀ {p} → Seq p → ℕ
slength (A , Γ) = _+_ (flength A) (clength' Γ)

infix 4 _<₂_

PolSeq : Set
PolSeq = Σ Pol Seq

pslength : PolSeq → ℕ
pslength (x ,' y) = slength {x} y

data _<₂_ : PolSeq → PolSeq → Set where
  only↑ : ∀ {A : Fml +} {p} {B : Fml p} {Γ} {Γ₁} → clength Γ <′ clength Γ₁
      → (- ,' ↑ A , Γ) <₂ (p ,' B , Γ₁)
  only↓ : ∀ {A : Fml -} {p} {B : Fml p} {Γ} {Γ₁} → clength Γ <′ clength Γ₁
      → (+ ,' ↓ A , Γ) <₂ (p ,' B , Γ₁)

import Induction.WellFounded as WF
open WF _<₂_ -- using (acc)

allAcc : ∀ x → Acc x
allAcc (- ,' M , Γ) = acc f
    where f : (y : Σ Pol Seq) → y <₂ (- ,' M , Γ) → Acc y
          f .(- ,' ↑ A , Γ') (only↑ {A} {.-} {.M} {Γ'} y) = {!y!}
          f .(+ ,' ↓ A , Γ') (only↓ {A} {.-} {.M} {Γ'} y) = {!!}
allAcc (+ ,' P , Γ) = {!!}

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
