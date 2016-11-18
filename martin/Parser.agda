{-# OPTIONS  --type-in-type --no-termination-check #-}
module Parser where

open import Category.Functor
open import Category.Monad
open import Data.Bool renaming (true to - ; false to +; Bool to Pol ; T to IsTrue)
open import Data.Char renaming (_==_ to _C==_)
open import Data.Empty
open import Data.Function
open import Data.List renaming ([_] to L[_])
open import Data.Maybe
open import Data.Nat
open import Data.Product renaming (_,_ to _,'_)
open import Data.String renaming (_++_ to _s++_)
open import Data.Sum
open import Data.Unit
open import Data.Unit
open import FFI.Int
open import FFI.Pair
open import Foreign.Haskell
open import Game renaming (_⊗_ to _⊗'_ ; _⊘_ to _⊘'_)
open import ParsePrint.ReadP
open import Relation.Binary.PropositionalEquality
open import WS-Syn
open import WS-Annot

open module dummy = RawMonadPlus monadR
  renaming (_⊗_ to _R⊗_)

lexeme : ∀ {a} → ReadP a → ReadP a
lexeme p = p >>= λ a → skipSpaces >> return a

lexchar = lexeme ∘ char
lexstr  = lexeme ∘ string

pMov : ∀ (ι : MovEnc) → ReadP (T ι)
pMov nil     = pfail
pMov one     = lexchar '0' >> return tt
pMov (ι ⊹ κ) = (lexchar 'L' >> inj₁ <$> pMov ι) +++
               (lexchar 'R' >> inj₂ <$> pMov κ)


parens : ∀ {a} → ReadP a → ReadP a
parens = between (lexchar '(') (lexchar ')')

binl  : ∀ {a} → ReadP a → Char → (a → a → a) → ReadP a
binl  p c f = chainl1 p (lexchar c >> return f)

binl' : ∀ {a b} → ReadP a → Char → (a → b → a) → ReadP b → ReadP a
binl' p c f q = p >>= λ P → foldl f P <$> many (lexchar c >> q)

mutual
  atom- = (lexstr "F1" >> return F1) +++ parens fml-
  atom+ = (lexstr "F0" >> return F0) +++ parens fml+
  p↑    = (lexchar '↑' >> ↑ <$> p↓) +++ atom-
  p↓    = (lexchar '↓' >> ↓ <$> p↑) +++ atom+
  p⊗    = binl  p↑ '⊗' _⊗_    
  p⅋    = binl  p↓ '⅋' _⅋_
  p⊕    = binl  p⅋ '⊕' _⊕_
  p&    = binl  p⊗ '&' _&_
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

pTop : ∀ {a} → ReadP a → ReadP a
pTop p = skipSpaces >> p >>= λ a → eof >> return a

Res_to_Maybe : ∀ {a} → Res a → Maybe a
Res_to_Maybe ((A ,' []) ∷ _) = just A
Res_to_Maybe _               = nothing

parseTop : ∀ {a} → ReadP a → String → Maybe a
parseTop p s = Res_to_Maybe $ readP_to_S (pTop p) (toList s)

parseFml : String → Maybe PolFml
parseFml = parseTop pFml


PolSeq = Σ _ Seq

pCtx : ReadP Ctx
pCtx = (pFml >>= λ pA → lexchar ',' >> comma pA <$> pCtx)
       +++
       (lexchar 'ε' >> return ε)
  where comma : PolFml → Ctx → Ctx
        comma (p ,' A) Γ = (A , Γ)

pSeq : ReadP PolSeq
pSeq = comma <$> pFml ⊛ (lexchar ',' >> pCtx)
  where comma : PolFml → Ctx → PolSeq
        comma (p ,' A) Γ = p ,' (A , Γ)

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
  pDer9 (F1 , Γ) = (lexstr "P1" >> return P1) +++ parens (pDer (F1 , Γ))
  pDer9 Γ        = parens (pDer Γ)

  pDer : ∀ {pol}(Γ : Seq pol) → ReadP (⊢ Γ)
  pDer (M ⊗ N , Γ) = dBin P⊗  "P⊗"
  pDer (P ⅋ Q , Γ) = dUna P⅋₁ "P⅋₁" +++ dUna P⅋₂ "P⅋₂" 
  pDer (P ⊕ Q , Γ) = dUna P⊕₁ "P⊕₁" +++ dUna P⊕₂ "P⊕₂"
  pDer (M & N , Γ) = dBin P&  "P&" 
  pDer (A ⊘ M , Γ) = dUna P⊘  "P⊘"
  pDer (A ◁ P , Γ) = dUna P◁  "P◁"
  pDer (↑ P , ε)             = dUna P↑  "P↑"
  pDer (↑ P , _,_ { - } N Γ) = dUna P↑- "P↑-"
  pDer (↑ P , _,_ { + } Q Γ) = dUna P↑+ "P↑+"
  pDer (↓ N , ε)             = dUna P↓  "P↓"
  pDer (↓ N , _,_ { + } P Γ) = dUna P↓+ "P↓+"
  pDer (↓ M , _,_ { - } N Γ) = dUna P↓- "P↓-"
  pDer Γ = pDer9 Γ

pPrf : ReadP Prf
pPrf = pSeq >>= λ pΓ → lexstr "⊣:" >> pPrf' pΓ where
  pPrf' : (pΓ : PolSeq) → ReadP Prf
  pPrf' (p ,' Γ) = _⊣:_ Γ <$> pDer Γ

parsePrf : String → Maybe Prf
parsePrf = parseTop pPrf

test1 = parsePrf "↑ (↓ F1 ⊕ ↓ F1) , ↓ (↑ F0 & ↑ F0) , ε ⊣: P↑+ (P↑ (P⅋₂ (P↓+ (P↓ (P◁ (P& (P↑+ (P↑ (P⅋₂ (P⊕₂ (P↓+ (P↓ (P◁ P1))))))) (P↑+ (P↑ (P⅋₂ (P⊕₁ (P↓+ (P↓ (P◁ P1))))))))))))) " 

foo2 : Prf
foo2 = F1 & F1 , ε ⊣: P& P1 P1

