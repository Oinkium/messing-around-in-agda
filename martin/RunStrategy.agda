{-# OPTIONS  --type-in-type --no-termination-check #-}

module RunStrategy where
-- in which we provide the machinery to interact with a running
-- strategy.

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Integer using () renaming (+_ to ℕtoℤ)
open import Data.List as L renaming (_++_ to _L++_)
open import Data.String renaming (_++_ to _s++_ ; _==_ to _s==_)
open import Data.Sum
open import Data.Unit

open import Foreign.Haskell
open import System.IO

open import Game
open import GenericPrompt
import ParserCore as PC
open import IOGame

-- Normalising move sets, and forcing moves

normalise : MovEnc → MovEnc
normalise nil = nil
normalise one = one
normalise (a ⊹ b) with normalise a | normalise b
...                  | nil   | X = X
...                  | one   | nil = one
...                  | one   | x ⊹ y = one ⊹ x ⊹ y
...                  | one   | one = one ⊹ one
...                  | one   | ℕ× x = one ⊹ ℕ× x
...                  | x ⊹ y | nil = x ⊹ y
...                  | x ⊹ y | one = x ⊹ y ⊹ one
...                  | x ⊹ y | u ⊹ v = x ⊹ y ⊹ u ⊹ v
...                  | x ⊹ y | ℕ× u = x ⊹ y ⊹ ℕ× u
...                  | ℕ× u | nil = ℕ× u
...                  | ℕ× u | one = ℕ× u ⊹ one
...                  | ℕ× u | x ⊹ y = ℕ× u ⊹ x ⊹ y
...                  | ℕ× u | ℕ× v = ℕ× u ⊹ ℕ× v
normalise (ℕ× a) with normalise a
...                  | nil = nil
...                  |  b  = ℕ× b

the-mv : ∀ {ι} -> one ≡ normalise ι → T ι
the-mv {nil} ()
the-mv {one} refl = tt
the-mv {x ⊹ y} eq with normalise x | normalise y | the-mv {x} | the-mv {y}
the-mv {x ⊹ y} eq    | nil         | ny    | mx | my = inj₂ (my eq)
the-mv {x ⊹ y} eq    | one         | nil   | mx | my = inj₁ (mx eq)
the-mv {x ⊹ y} ()    | one         | one   | mx | my 
the-mv {x ⊹ y} ()    | one         | _ ⊹ _ | mx | my 
the-mv {x ⊹ y} ()    | one         | ℕ× _  | mx | my
the-mv {x ⊹ y} ()    | _ ⊹ _       | nil   | mx | my
the-mv {x ⊹ y} ()    | _ ⊹ _       | one   | mx | my
the-mv {x ⊹ y} ()    | _ ⊹ _       | _ ⊹ _ | mx | my
the-mv {x ⊹ y} ()    | _ ⊹ _       | ℕ× _  | mx | my
the-mv {x ⊹ y} ()    | ℕ× _        | nil   | mx | my
the-mv {x ⊹ y} ()    | ℕ× _        | one   | mx | my
the-mv {x ⊹ y} ()    | ℕ× _        | _ ⊹ _ | mx | my
the-mv {x ⊹ y} ()    | ℕ× _        | ℕ× _  | mx | my
the-mv {ℕ× e} eq with normalise e | the-mv {e}
the-mv {ℕ× e} () | nil   | me
the-mv {ℕ× e} () | one   | me
the-mv {ℕ× e} () | _ ⊹ _ | me
the-mv {ℕ× e} () | ℕ× _  | me

-- Running a Strategy

indent2 = nest (ℕtoℤ 2)

mutual

  Ask :  ∀ {G A} → Strat - G → Annotation G (λ _ → A) → (A → Doc) → IO Unit
  Ask {gam {mov} f} (neg s) (ν a g) sh with normalise mov | the-mv {mov}
  ...           | nil | _  = putDocLn (text "You lose, inevitably.")
  ...           | one | tm = putDocLn (sep (text "Your choice is forced in"
                                   ∷ indent2 (sh a) ∷ [])) >>
                                  Tell (s $ tm refl) (g $ tm refl) sh
  ...           | _   | _  = Ask' {gam {mov} f} (neg s) (ν a g) sh 


  Ask' : ∀ {G A} → Strat - G → Annotation G (λ _ → A) → (A → Doc) → IO Unit
  Ask' {gam {ι}   f} (neg s) (ν a g) show =
    prompt (sep (text "Your choice in '" <> prMovEnc ι <> text "'" ∷
                 indent2 (text "encoding " <> show a) ∷
                 text "(options are " <> descMoves ι <> text ")"∷ []))
           (PC.parseTop (pMov ι))
           (λ i → Tell (s i) (g i) show)

  Tell : ∀ {G A} → (Strat +) G → Annotation G (λ _ → A) → (A → Doc) → IO Unit
  Tell {gam {ι} f} (pos i s) (ν a g) show =
     putDocLn (sep (text "My choice in '" <> prMovEnc ι <> text "'" ∷
                 indent2 (text "encoding " <> show a) ∷
                 indent2 (text "is " <> prMov ι i) ∷ [])) >>
     Ask s (g i) show

{-
runprf : ∀ {p}{Γ : Seq p} → ⊢ Γ → IO Unit
runprf { - } {Γ} prf = Ask  ⟦ prf ⟧⊢ (anotate $ Γ F) (prFml ∘ proj₂)
runprf { + } {Γ} prf = Tell ⟦ prf ⟧⊢ (anotate $ Γ F) (prFml ∘ proj₂)
-}
-- Old code:


{-

prFmlGame {pol} A =
  prPol pol <> PP.char ':' <> prFml A $$
  nest (ℕtoℤ 2) 
    (vcat (L.map (λ i → prFmlGame (annot A i)) (listMovEnc (mvEnc ⟦ A ⟧))))

  Ask {gam {mov} f} (neg s) (ν a g) sh with inspect (normalise mov)
  ...           | nil with-≡ _  = putDocLn (text "You lose, inevitably.")
  ...           | one with-≡ eq = putDocLn (sep (text "Your choice is forced in"
                                   ∷ indent2 (sh a) ∷ [])) >>
                                  Tell (s $ the-mv eq) (g $ the-mv eq) sh
  ...           | mr with-≡ _   = Ask' {gam {mov} f} (neg s) (ν a g) sh 


  Tell {gam {ι} f} (pos i s) =
     putDocLn ((text "My choice in " <> prettyMovEnc ι <> text " is ") $$
               prettyTMovEnc ι i) >>
     Ask s
-}

