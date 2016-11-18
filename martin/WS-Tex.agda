{-# OPTIONS  --type-in-type --no-termination-check #-}

module WS-Tex where
-- converting WS proofs into latex

open import Data.Char
open import Data.Integer using () renaming (+_ to ℕtoℤ)
open import Data.List as L renaming (_++_ to _L++_)
open import Data.String
open import Data.Sum
open import Data.Unit
open import Function
open import Data.Product renaming (_,_ to _,'_)
open import Data.Maybe

open import Foreign.Haskell
open import ParsePrint.PrettyPrint as PP

open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import WS-Syn
open import WS-Annot
open import WS-Sem-Fsc

f2tex : ∀ {p} → Fml p → Doc
f2tex F0 = text "\\mathbf{0}"
f2tex F1 = text "\\mathbf{1}"
--f2tex (↑ P) = text "\\uparrow" <> f2tex P
--f2tex (↓ M) = text "\\downarrow" <> f2tex M
f2tex F⊤ = text "F⊤"
f2tex F⊥ = text "F⊥"
f2tex (M ⊗ N) = text "(" <> f2tex M <> text " \\otimes " <> f2tex N <> text ")"
f2tex (P ⅋ Q) = text "(" <> f2tex P <> text " \\parr " <> f2tex Q <> text ")"
f2tex (P ⊕ Q) = text "(" <> f2tex P <> text " \\oplus " <> f2tex Q <> text ")"
f2tex (M & N) = text "(" <> f2tex M <> text "\\&" <> f2tex N <> text ")"
f2tex (A ⊘ M) = text "(" <> f2tex A <> text " \\oslash " <> f2tex M <> text ")"
f2tex (A ◁ P) = text "(" <> f2tex A <> text " \\lhd " <> f2tex P <> text ")"
f2tex (ω& N) = text "\\omega\\&" <> f2tex N
f2tex (ω⊕ P) = text "\\omega\\oplus" <> f2tex P

s2tex : ∀ {p} → Seq p → Doc
s2tex (A , ε)     = f2tex A
s2tex (A , B , Γ) = f2tex A <> text " , " <> s2tex (B , Γ)

shownat = PP.primShowInteger ∘ PP.primNatToInteger

mutual
  una : ∀ {p q} {Γ : Seq p} → ⊢ Γ → Seq q → String → Doc
  una prf Δ s = ⊢2tex prf
    <> text " \\LeftLabel{$" <> text s <> text "$} "
    <> text " \\UnaryInfC{$ \\vdash " <> s2tex Δ <> text "$} "

  bina : ∀ {p q r} {Γ : Seq p} {Γ₁ : Seq r} → ⊢ Γ → ⊢ Γ₁ → Seq q → String → Doc
  bina prf prf2 Δ s = ⊢2tex prf <> ⊢2tex prf2
    <> text " \\LeftLabel{$" <> text s <> text "$} "
    <> text " \\BinaryInfC{$ \\vdash " <> s2tex Δ <> text "$} "

  nulla : ∀ {q} → Seq q → String → Doc
  nulla Δ s = text " \\AxiomC{} "
                     <> text " \\LeftLabel{$" <> text s <> text "$} "
                     <> text " \\UnaryInfC{$ \\vdash " <> s2tex Δ <> text "$} "

  ⊢2tex' : ∀ p → (Γ : Seq p) → ⊢ Γ → Doc
  ⊢2tex' .- .(F1 , Γ) (P1 {Γ}) = nulla (F1 , Γ) "\\p \\mathbf{1}"
  ⊢2tex' .+ .(F⊤ , ε) (P⊤) = nulla (F⊤ , ε) "\\p \\top"
  ⊢2tex' .- .(M ⊗ N , Γ) (P⊗ {M} {N} {Γ} y y') = bina y y' (M ⊗ N , Γ) "\\p \\otimes"
  ⊢2tex' .+ .(P ⅋ Q , Γ) (P⅋₁ {P} {Q} {Γ} y) = una y (P ⅋ Q , Γ) "\\p \\parr_1"
  ⊢2tex' .+ .(P ⅋ Q , Γ) (P⅋₂ {P} {Q} {Γ} y) = una y (P ⅋ Q , Γ) "\\p \\parr_2"
  ⊢2tex' .+ .(P ⊕ Q , Γ) (P⊕₁ {P} {Q} {Γ} y) = una y (P ⊕ Q , Γ) "\\p \\oplus_1"
  ⊢2tex' .+ .(P ⊕ Q , Γ) (P⊕₂ {P} {Q} {Γ} y) = una y (P ⊕ Q , Γ) "\\p \\oplus_2"
  ⊢2tex' .+ .(ω⊕ P , Γ) (P⊕ω {P} {Γ} n y) = una y (ω⊕ P , Γ) ("\\p \\oplus_\\omega^" ++ shownat n)
  ⊢2tex' .- .(M & N , Γ) (P& {M} {N} {Γ} y y') = bina y y' (M & N , Γ) "\\p \\&"
  ⊢2tex' .- .(ω& N , Γ) (P&ω {N} {Γ} y) = bina (y 1) (y 2) (ω& N , Γ) "\\p \\&\\omega"
  ⊢2tex' .- .(F⊥ , P , ε) (P⊥+ {P} y) = una y (F⊥ , P , ε) "\\p \\bot +"
  ⊢2tex' .- .(F⊥ , N , Γ) (P⊥- {N} {Γ} y) = una y (F⊥ , Γ) "\\p \\bot -"
  ⊢2tex' .- .(F⊥ , P , N , Γ) (P⊥⊘ {P} {N} {Γ} y) = una y (F⊥ , P , N , Γ) "\\p \\bot \\oslash"
  ⊢2tex' .- .(F⊥ , P , Q , Γ) (P⊥⅋ {P} {Q} {Γ} y) = una y (F⊥ , P , Q , Γ) "\\p \\bot \\parr"
  ⊢2tex' .+ .(F⊤ , N , ε) (P⊤- {N} y) = una y (F⊤ , N , ε) "\\p \\top -"
  ⊢2tex' .+ .(F⊤ , P , Γ) (P⊤+ {P} {Γ} y) = una y (F⊤ , Γ) "\\p \\top +"
  ⊢2tex' .+ .(F⊤ , N , P , Γ) (P⊤◁ {N} {P} {Γ} y) = una y (F⊤ , N , P , Γ) "\\p \\top \\lhd"
  ⊢2tex' .+ .(F⊤ , M , N , Γ) (P⊤⊗ {M} {N} {Γ} y) = una y (F⊤ , M , N , Γ) "\\p \\top \\otimes"
  ⊢2tex' p .(A ⊘ M , Γ) (P⊘ {.p} {A} {M} {Γ} y) = una y (A ⊘ M , Γ) "\\p \\oslash"
  ⊢2tex' p .(A ◁ P , Γ) (P◁ {.p} {A} {P} {Γ} y) = una y (A ◁ P , Γ) "\\p \\lhd"
  ⊢2tex' p .(Γ ,,₀ (F1 , Δ)) (P1T {.p} {Γ} {Δ} y) = una y (Γ ,,₀ (F1 , Δ)) "\\p_{\\mathbf{1}}^\\top"
  ⊢2tex' p .(Γ ,,₀ Δ) (P1Tb {.p} {Γ} {Δ} y) = una y (Γ ,,₀ Δ) "\\p_{\\mathbf{1}}^\\top"
  ⊢2tex' p .(Γ ,,₀ (F0 , Δ)) (P0T {.p} {Γ} {Δ} y) = una y (Γ ,,₀ (F0 , Δ)) "\\p_{\\mathbf{0}}^\\top"
  ⊢2tex' p .(Γ ,,₀ Δ) (P0Tb {.p} {Γ} {Δ} y) =  una y (Γ ,,₀ Δ) "\\p_{\\mathbf{0}}^\\top"
  ⊢2tex' p .(Γ ,,₀ (M ⊗ N , Δ)) (P⊗T {.p} {M} {N} {Δ} {Γ} y) = una y (Γ ,,₀ (M ⊗ N , Δ)) "\\p_{\\otimes}^\\top"
  ⊢2tex' p .(Γ ,,₀ (M , N , Δ)) (P⊗Tb {.p} {M} {N} {Δ} {Γ} y) = una y (Γ ,,₀ (M , N , Δ)) "\\p_{\\otimes}^\\top" 
  ⊢2tex' p .(Γ ,,₀ (P ⅋ Q , Δ)) (P⅋T {.p} {P} {Q} {Δ} {Γ} y) = una y (Γ ,,₀ (P ⅋ Q , Δ)) "\\p_{\\parr}^\\top" 
  ⊢2tex' p .(Γ ,,₀ (P , Q , Δ)) (P⅋Tb {.p} {P} {Q} {Δ} {Γ} y) = una y (Γ ,,₀ (P , Q , Δ)) "\\p_{\\parr}^\\top"
  ⊢2tex' p .(Γ ,,₀ (P ⊕ Q , Δ)) (P⊕T₁ {.p} {P} {Q} {Δ} {Γ} y) = una y (Γ ,,₀ (P ⊕ Q , Δ)) "\\p_{\\oplus}^\\top_1"
  ⊢2tex' p .(Γ ,,₀ (P ⊕ Q , Δ)) (P⊕T₂ {.p} {P} {Q} {Δ} {Γ} y) = una y (Γ ,,₀ (P ⊕ Q , Δ)) "\\p_{\\oplus}^\\top_2"
  ⊢2tex' p .(Γ ,,₀ (ω⊕ P , Δ)) (P⊕Tω {.p} {P} {Δ} {Γ} n y) = una y (Γ ,,₀ (ω⊕ P , Δ)) ("\\p_{\\oplus}^\\top_" ++ shownat n)
  ⊢2tex' p .(Γ ,,₀ (B , A , Δ)) (Psym {.p} {q} {Δ} {Γ} {A} {B} y) =  una y (Γ ,,₀ (B , A , Δ)) "\\p_{\\sym}^\\top_1"
  ⊢2tex' p .(Γ ,,₀ (P , Δ)) (Pstr {.p} {Δ} {Γ} {P} y) = una y (Γ ,,₀ (P , Δ)) "\\p_{\\mathsf{str}}^\\top"
  ⊢2tex' p .(Γ ,,₀ Δ) (Pwk {.p} {Δ} {Γ} y) = una y (Γ ,,₀ Δ) "\\p_{\\mathsf{wk}}^\\top"
  ⊢2tex' p .(Γ ,,₀ Δ ,,₀ Γ₁) (Pcut {.p} {Δ} {Γ₁} {Γ} y y' y0) = bina y' y0 (Γ ,,₀ Δ ,,₀ Γ₁) "\\p\\mathsf{cut}"
  ⊢2tex' .+ .(Q , ε) (Pcut0 {N} {Q} y y') = bina y y' (Q , ε) "\\p\\mathsf{cut}0"
  ⊢2tex' .- .(M , Γ ,,₀ P ⊘ N , Δ) (P⊸ {M} {Γ} {P} {N} {Δ} Δ+ y y') = bina y y' (M , Γ ,,₀ P ⊘ N , Δ) "\\p\\multimap"
  ⊢2tex' .- .(M , N , (M ⊥') ◁ Q , Γ) (Pid⊘ {M} {N} {Q} {Γ} y y0) = una y0 (M , N , (M ⊥') ◁ Q , Γ) "\\p\\id\\oslash"
  ⊢2tex' .- .(M , M ⊥' , ε) (Pid {M}) = nulla (M , M ⊥' , ε) "\\p\\mathsf{id}"
  ⊢2tex' .- .(M , ((Γ ,, N , Γ₁) ,, Δ) ,, Δ₁) (Pmix {Γ} {Δ} {Δ₁} {Γ₁} {N} {M} y y' Γ₁' y0 y1) = bina y0 y1 (M , ((Γ ,, N , Γ₁) ,, Δ) ,, Δ₁) "\\p\\mathsf{mix}"

  ⊢2tex : ∀ {p} {Γ : Seq p} → ⊢ Γ → Doc
  ⊢2tex {p} {Γ} q = ⊢2tex' p Γ q

prf2tex : ∀ {p} {Γ : Seq p} → ⊢ Γ → Doc
prf2tex prf = text "\\begin{prooftree} " <> ⊢2tex prf <> text " \\end{prooftree}"