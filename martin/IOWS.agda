{-# OPTIONS --type-in-type --no-termination-check #-}

module IOWS where
-- in which we provide functions for printing and parsing
-- proofs/formulas

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

open import ParserCore as PC

ErrorMsg = Doc

prFml : ∀ {p} → Fml p → Doc
prFml F0    = text "F0"
prFml F1    = text "F1"
prFml F⊥    = text "F⊥"
prFml F⊤    = text "F⊤"
prFml A     = PP.parens $ pr A
  where 
  prbin : ∀{p}(A : Fml p)(c : Char){q}(B : Fml q) → Doc
  prbin A c B = sep (prFml A ∷ PP.char c ∷ prFml B ∷ [])
  pr : ∀ {p} → Fml p → Doc
  pr F⊤      = text "F⊤"
  pr F⊥      = text "F⊥" 
  pr (ω⊕ P)  = text "ω⊕" <> prFml P
  pr (ω& M)  = text "ω&" <> prFml M
  pr (M ⊗ N) = prbin M '⊗' N
  pr (P ⅋ Q) = prbin P '⅋' Q
  pr (A ⊘ M) = prbin A '⊘' M
  pr (A ◁ P) = prbin A '◁' P
  pr (P ⊕ Q) = prbin P '⊕' Q
  pr (M & N) = prbin M '&' N
  pr F0      = text "F0"
  pr F1      = text "F1"

prCtx' : Ctx → List Doc
prCtx' ε       = text "ε" ∷ []
prCtx' (A , Γ) = prFml A ∷ prCtx' Γ

prSeq : ∀ {p} → Seq p → Doc
prSeq (A , Γ) = sep (comma' (prFml A ∷ prCtx' Γ)) where
  comma' : List Doc → List Doc
  comma' [] = []
  comma' (p ∷ []) = p ∷ []
  comma' (p ∷ ps) = (p <> PP.char ',') ∷ comma' ps

shownat = PP.primShowInteger ∘ PP.primNatToInteger


prDer : ∀ {pol}{Γ : Seq pol}(prf : ⊢ Γ) → Doc
prDer P1  = text "P1"
prDer P⊤  = text "P⊤"
prDer prf = PP.parens (pr prf) where
  bin : ∀{pol₁ pol₂}{Γ : Seq pol₁}{Δ : Seq pol₂}
           (str : String)(d : ⊢ Γ)(e : ⊢ Δ) → Doc
  bin str d e = sep (text str ∷ prDer d ∷ prDer e ∷ [])
  una : ∀{pol}{Γ : Seq pol}(str : String)(d : ⊢ Γ) → Doc
  una str d = sep (text str ∷ prDer d ∷ [])
  pr :  ∀ {pol}{Γ : Seq pol}(prf : ⊢ Γ) → Doc
  pr P1 = text "P1"
  pr P⊤ = text "P⊤"
  pr (P⊗ y y') = bin "P⊗" y y'
  pr (P& y y') = bin "P&" y y'
  pr (P&ω y) = bin "P&"  (y 0) (y 1)
  pr (P⊥+ y) = una "P⊥+" y
  pr (P⊥- y) = una "P⊥-" y
  pr (P⊥⊘ y) = una "P⊥⊘" y
  pr (P⊥⅋ y) = una "P⊥⅋" y
  pr (P⅋₁ y) = una "P⅋₁" y
  pr (P⅋₂ y) = una "P⅋₂" y
  pr (P⊕₁ y) = una "P⊕₁" y
  pr (P⊕₂ y) = una "P⊕₂" y
  pr (P⊕ω y y') = una ("P⊕" ++ shownat y) y'
  pr (P⊤+ y) = una "P⊤+" y
  pr (P⊤- y) = una "P⊤-" y
  pr (P⊤◁ y) = una "P⊤◁" y
  pr (P⊤⊗ y) = una "P⊤⊗" y
  pr (P⊘ y) = una "P⊘" y
  pr (P◁ y) = una "P◁" y
  pr (P1T y) = una "P1T" y
  pr (P1Tb y) = una "P1Tb" y
  pr (P0T y) = una "P0T" y
  pr (P0Tb y) = una "P0Tb" y
  pr (P⊗T y) = una "P⊗T" y
  pr (P⊗Tb y) = una "P⊗Tb" y
  pr (P⅋T y) = una "P⅋T" y
  pr (P⅋Tb y) = una "P⅋Tb" y
  pr (P⊕T₁ y) = una "P⊕T₁" y
  pr (P⊕T₂ y) = una "P⊕T₂" y
  pr (P⊕Tω y y') = una ("P⊕T" ++ shownat y) y' 
  pr (Psym y) = una "Psym" y
  pr (Pstr y) = una "Pstr" y
  pr (Pwk y) = una "Pwk" y
  pr (Pcut _ y' y0) = bin "Pcut" y' y0
  pr (Pcut0 y y') = bin "Pcut0" y y'
  pr Pid = text "Pid"
  pr (Pmix _ _ _ y0 y1) = bin "Pmix" y0 y1
  pr (Pid⊘ y y') = una "Pid⊘" y'
  pr (P⊸ y y' y0) = bin "P⊸" y' y0


prPrf : Prf → Doc
prPrf (Γ ⊣: prf) = sep (prSeq Γ ∷ text "⊣:" ∷ prDer prf ∷ [])

mutual
  prbin1 : ∀{p q G H}(A : FML p G)(i : Mov G)(c : String)(B : FML q H) → Doc
  prbin1 A i c B = sep (prFMLFoc A i ∷ text c ∷ prFml (toFml B) ∷ [])
  prbin2 : ∀{p q G H}(A : FML p G)(c : String)(B : FML q H)(j : Mov H) → Doc
  prbin2 A c B j = sep (prFml (toFml A) ∷ text c ∷ prFMLFoc B j ∷ [])

  prFMLFoc' : ∀{p G}(A : FML p G)(i : Mov G) → Doc
  prFMLFoc' F⊤ i = text "⊤"
  prFMLFoc' F⊥ i = text "⊥"
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
  prFMLFoc X  i = PP.parens $ prFMLFoc' X i


prFmlFoc : ∀ {p}(A : Fml p)(i : Mov ⟦ A ⟧) → Doc
prFmlFoc A i = prFMLFoc (toFML A) i

prFML : ∀ {p G} → FML p G → Doc
prFML A = prFml (toFml A)

pMov : ∀ (ι : MovEnc) → ReadP (T ι)
pMov nil     = pfail
pMov one     = lexchar '0' >> return tt
pMov (ι ⊹ κ) = (lexchar 'L' >> inj₁ <$> pMov ι) +++
               (lexchar 'R' >> inj₂ <$> pMov κ)
pMov (ℕ× ι)  = lexnum >>= (λ n → (λ x → (n ,' x)) <$> pMov ι)

mutual
  atom- = (lexstr "F1" >> return F1) +++ PC.parens fml-
  atom+ = (lexstr "F0" >> return F0) +++ PC.parens fml+
  p↑    = (lexchar '↑' >> ↑ <$> p↓) +++ atom-
  p↓    = (lexchar '↓' >> ↓ <$> p↑) +++ atom+
  p⊗    = binl  p↑ '⊗' _⊗_    
  p⅋    = binl  p↓ '⅋' _⅋_
  p⊕    = binl  p⅋ '⊕' _⊕_
  p&    = binl  p⊗ 'ω' _&_

  p+⊘   = binl' p⊕ '⊘' _⊘_ p&
  p-⊘   = binl  p& '⊘' _⊘_
  p+◁   = binl  p⊕ '◁' _◁_
  p-◁   = binl' p& '◁' _◁_ p⊕

  fml+ : ReadP (Fml +)
  fml+ = p+⊘ +++ p+◁

  fml- : ReadP (Fml -)
  fml- = p-⊘ +++ p-◁

pFml : ReadP PolFml
pFml = (_,'_ + <$> fml+) +++ (_,'_ - <$> fml-) 

parseFml : String → Maybe PolFml
parseFml = parseTop pFml

pCtx : ReadP Ctx
pCtx = (pFml >>= λ pA → lexchar ',' >> comma' pA <$> pCtx)
       +++
       (lexchar 'ε' >> return ε)
  where comma' : PolFml → Ctx → Ctx
        comma' (p ,' A) Γ = (A , Γ)

pSeq : ReadP PolSeq
pSeq = comma' <$> pFml ⊛ (lexchar ',' >> pCtx)
  where comma' : PolFml → Ctx → PolSeq
        comma' (p ,' A) Γ = p ,' (A , Γ)

parseSeq : String → Maybe PolSeq
parseSeq = parseTop pSeq

mutual
  dUna : ∀{p q}{Γ : Seq p}{Δ : Seq q}(op : ⊢ Δ → ⊢ Γ) str  → ReadP (⊢ Γ)
  dUna {Γ = Γ}{Δ} op str = (lexstr str >> op <$> pDer9 Δ) +++ pDer9 Γ

  dBin : ∀ {p q r}{Γ : Seq p}{Δ : Seq q}{θ : Seq r}
           (op : ⊢ Δ → ⊢ θ → ⊢ Γ) str → ReadP (⊢ Γ)
  dBin {Γ = Γ}{Δ}{θ} op str = (lexstr str >> op <$> pDer9 Δ ⊛ pDer9 θ)
                              +++ pDer9 Γ

  pDer9 : ∀ {pol}(Γ : Seq pol) → ReadP (⊢ Γ)
  pDer9 (F1 , Γ) = (lexstr "P1" >> return P1) +++ PC.parens (pDer (F1 , Γ))
  pDer9 Γ        = PC.parens (pDer Γ)

  pDer : ∀ {pol}(Γ : Seq pol) → ReadP (⊢ Γ)
  pDer (M ⊗ N , Γ) = dBin P⊗  "P⊗"
  pDer (P ⅋ Q , Γ) = dUna P⅋₁ "P⅋₁" +++ dUna P⅋₂ "P⅋₂" 
  pDer (P ⊕ Q , Γ) = dUna P⊕₁ "P⊕₁" +++ dUna P⊕₂ "P⊕₂"
  pDer (M & N , Γ) = dBin P&  "P&" 
  pDer (A ⊘ M , Γ) = dUna P⊘  "P⊘"
  pDer (A ◁ P , Γ) = dUna P◁  "P◁"
  pDer (F⊥ , _,_ { - } N Γ)     = dUna P⊥-  "P⊥-"
  pDer (F⊥ , _,_ { + } P ε)                 = dUna P⊥+  "P⊥+"
  pDer (F⊥ , _,_ { + } P (_,_ { - } N Γ)) = dUna P⊥⊘  "P⊥⊘-"
  pDer (F⊥ , _,_ { + } P (_,_ { + } Q Γ)) = dUna P⊥⅋  "P⊥⅋"
  pDer (F⊤ , _,_ { + } P Γ)             = dUna P⊤+  "P⊤+"
  pDer (F⊤ , _,_ { - } N ε)             = dUna P⊤-  "P⊤-"
  pDer (F⊤ , _,_ { - } N (_,_ { + } P Γ)) = dUna P⊤◁  "P⊤◁"
  pDer (F⊤ , _,_ { - } M (_,_ { - } N Γ)) = dUna P⊤⊗  "P⊤⊗"
  pDer Γ = pDer9 Γ

pPrf : ReadP Prf
pPrf = pSeq >>= λ pΓ → lexstr "⊣:" >> pPrf' pΓ where
  pPrf' : (pΓ : PolSeq) → ReadP Prf
  pPrf' (p ,' Γ) = _⊣:_ Γ <$> pDer Γ

parsePrf : String → Maybe Prf
parsePrf = parseTop pPrf
