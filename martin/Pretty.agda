module Pretty where

open import Data.Bool renaming (true to - ; false to + ;
                                Bool to Pol ; T to IsTrue)
open import Data.Char
open import Data.Empty
open import Data.Function
open import Data.Integer using () renaming (+_ to ℕtoℤ)
open import Data.List as L renaming (_++_ to _L++_)
open import Data.Maybe
open import Data.String
open import Data.Sum
open import Data.Unit
open import Data.Nat
open import Foreign.Haskell

open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import ParsePrint.PrettyPrint
open import Relation.Binary.PropositionalEquality
open import System.IO
open import WS-Syn
open import WS-Sem-Fsc
open import WS-Annot

ErrorMsg = Doc

prMovEnc : MovEnc → Doc
prMovEnc nil     = text "nil" 
prMovEnc one     = text "one"
prMovEnc (i ⊹ j) = parens (prMovEnc i <> text " + " <> prMovEnc j)

prMov : (i : MovEnc) → T i → Doc
prMov i x =  text (fromList (prMov' i x))
  where
  prMov' : (i : MovEnc) → T i → List Char
  prMov' nil     ()
  prMov' one     _           = '0' ∷ []
  prMov' (i ⊹ j) (inj₁ x)    = 'L' ∷ prMov' i x
  prMov' (i ⊹ j) (inj₂ y)    = 'R' ∷ prMov' j y

    
prPol : Pol → Doc
prPol + = text "+"
prPol - = text "-"

prFml : ∀ {p} → Fml p → Doc
prFml F0    = text "F0"
prFml F1    = text "F1"
prFml A     = parens $ pr A
  where 
  prbin : ∀{p}(A : Fml p)(c : Char){q}(B : Fml q) → Doc
  prbin A c B = sep (prFml A ∷ char c ∷ prFml B ∷ [])
  pr : ∀ {p} → Fml p → Doc
  pr (↑ P)   = char '↑' <> prFml P
  pr (↓ M)   = char '↓' <> prFml M
  pr (M ⊗ N) = prbin M '⊗' N
  pr (P ⅋ Q) = prbin P '⅋' Q
  pr (A ⊘ M) = prbin A '⊘' M
  pr (A ◁ P) = prbin A '◁' P
  pr (P ⊕ Q) = prbin P '⊕' Q
  pr (M & N) = prbin M '&' N
  pr F0      = text "F0" -- impossible
  pr F1      = text "F1" -- impossible

prGame : Pol → Game → Doc
prGame p (gam {a} f) = 
  prPol p <> char ':' <> prMovEnc a $$
  nest (ℕtoℤ 2)
   (vcat (L.map (λ i → prGame (not p) (f i)) (listMovEnc a)))

{-
putDocLn : Doc → IO Unit
putDocLn = putStrLn' ∘ render
-}

prCtx' : Ctx → List Doc
prCtx' ε       = text "ε" ∷ []
prCtx' (A , Γ) = prFml A ∷ prCtx' Γ

prSeq : ∀ {p} → Seq p → Doc
prSeq (A , Γ) = sep (comma' (prFml A ∷ prCtx' Γ)) where
  comma' : List Doc → List Doc
  comma' [] = []
  comma' (p ∷ []) = p ∷ []
  comma' (p ∷ ps) = (p <> char ',') ∷ comma' ps

prDer : ∀ {pol}{Γ : Seq pol}(prf : ⊢ Γ) → Doc
prDer P1  = text "P1"
prDer prf = parens (pr prf) where
  bin : ∀{pol₁ pol₂}{Γ : Seq pol₁}{Δ : Seq pol₂}
           (str : String)(d : ⊢ Γ)(e : ⊢ Δ) → Doc
  bin str d e = sep (text str ∷ prDer d ∷ prDer e ∷ [])
  una : ∀{pol}{Γ : Seq pol}(str : String)(d : ⊢ Γ) → Doc
  una str d = sep (text str ∷ prDer d ∷ [])
  pr :  ∀ {pol}{Γ : Seq pol}(prf : ⊢ Γ) → Doc
  pr (P⊗  d e)   = bin "P⊗"  d e
  pr (P⅋₁ d)     = una "P⅋₁" d
  pr (P⅋₂ d)     = una "P⅋₂" d
  pr (P⊕₁ d)     = una "P⊕₁" d
  pr (P⊕₂ d)     = una "P⊕₂" d
  pr (P&  d e)   = bin "P&"  d e
  pr (P⊘  d)     = una "P⊘"  d
  pr (P◁  d)     = una "P◁"  d
  pr (P↑  d)     = una "P↑"  d
  pr (P↑- d)     = una "P↑-" d
  pr (P↑+ d)     = una "P↑+" d
  pr (P↓  d)     = una "P↓"  d
  pr (P↓+ d)     = una "P↓+" d
  pr (P↓- d)     = una "P↓+" d
  pr (P1T d)     = una "P1T" d
  pr (P0T d)     = una "P0T" d
  pr (P⊗T d)     = una "P⊗T" d
  pr (P⅋T d)     = una "P⅋T" d
  pr (P1Tb d)    = una "P1Tb" d
  pr (P0Tb d)    = una "P0Tb" d
  pr (P⊗Tb d)    = una "P⊗Tb" d
  pr (P⅋Tb d)    = una "P⅋Tb" d
  pr (P⊤b d)     = una "P⊤b" d
  pr (P⊥b d)     = una "P⊥b" d
  pr (P⊥ d)      = una "P⊥" d
  pr (P⊤ d)      = una "P⊤" d
  pr (P⊕T₁ d)    = una "P⊕T₁" d
  pr (P⊕T₂ d)    = una "P⊕T₂" d
  pr (Psym d)    = una "Psym" d
  pr (Pstr d)    = una "Pstr" d
  pr (Pwk d)     = una "Pwk" d
  pr Pid         = text "Pid"
  pr P1          = text "P1" -- impossible
  pr (Pcut _ d e ) = bin "Pmix"  d e
  pr (Pmix _ _ _ d e ) = bin "Pcut"  d e

prPrf : Prf → Doc
prPrf (Γ ⊣: prf) = sep (prSeq Γ ∷ text "⊣:" ∷ prDer prf ∷ [])

mutual
  prbin1 : ∀{p q G H}(A : FML p G)(i : Mov G)(c : String)(B : FML q H) → Doc
  prbin1 A i c B = sep (prFMLFoc A i ∷ text c ∷ prFml (toFml B) ∷ [])
  prbin2 : ∀{p q G H}(A : FML p G)(c : String)(B : FML q H)(j : Mov H) → Doc
  prbin2 A c B j = sep (prFml (toFml A) ∷ text c ∷ prFMLFoc B j ∷ [])

  prFMLFoc' : ∀{p G}(A : FML p G)(i : Mov G) → Doc
  prFMLFoc' (↑ P) i = text "↑" <> brackets (prFml (toFml P))
  prFMLFoc' (↓ M) i = text "↑" <> brackets (prFml (toFml M))
  prFMLFoc' (_⊗_ {gam _}{gam _} M N) (inj₁ i) = prbin1 M i "⊗" N
  prFMLFoc' (_⊗_ {gam _}{gam _} M N) (inj₂ j) = prbin2 M "⊗" N j
  prFMLFoc' (_⅋_ {gam _}{gam _} P Q) (inj₁ i) = prbin1 P i "⅋" Q
  prFMLFoc' (_⅋_ {gam _}{gam _} P Q) (inj₂ j) = prbin2 P "⅋" Q j 
  prFMLFoc' (_&_ {gam _}{gam _} M N) (inj₁ i) = prbin1 M i "&" N
  prFMLFoc' (_&_ {gam _}{gam _} M N) (inj₂ j) = prbin2 M "&" N j
  prFMLFoc' (_⊕_ {gam _}{gam _} P Q) (inj₁ i) = prbin1 P i "⊕" Q 
  prFMLFoc' (_⊕_ {gam _}{gam _} P Q) (inj₂ j) = prbin2 P "⊕" Q j
  prFMLFoc' (_-⊘_{gam _}{gam _} M N) i        = prbin1 M i "⊘" N
  prFMLFoc' (_+◁_{gam _}{gam _} P Q) i        = prbin1 P i "◁" Q
  prFMLFoc' (_+⊘_{gam _}{gam _} P N) i        = prbin1 P i "⊘" N
  prFMLFoc' (_-◁_{gam _}{gam _} M P) i        = prbin1 M i "◁" P
  prFMLFoc' _ i = text "(Pretty.prFMLFoc : impossible)"

  prFMLFoc : ∀{p}{G}(A : FML p G)(i : Mov G) → Doc
  prFMLFoc F0 ()
  prFMLFoc F1 ()
  prFMLFoc X  i = parens $ prFMLFoc' X i

prFmlFoc : ∀ {p}(A : Fml p)(i : Mov ⟦ A ⟧) → Doc
prFmlFoc A i = prFMLFoc (toFML A) i

prFML : ∀ {p G} → FML p G → Doc
prFML A = prFml (toFml A)
