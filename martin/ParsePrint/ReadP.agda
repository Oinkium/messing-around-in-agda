{-# OPTIONS --type-in-type --no-termination-check #-}
module ParsePrint.ReadP where

{-# IMPORT Data.Char #-}

open import Category.Functor
open import Category.Monad
open import Data.Bool
open import Data.Char renaming (_==_ to _C==_)
open import Function
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.String renaming (_++_ to _s++_)
open import Data.Unit
open import Foreign.Haskell
open import FFI.Pair
open import FFI.Int

{- NOTE:
   For the documentation of the Haskell ReadP, see 
   file://agda2/ghc-6.10.4/doc/libraries/base/Text-ParserCombinators-ReadP.html

   Needs to add for Data.List.List
   COMPILED_DATA List [] [] (:)

   Needs to add for Data.Bool.Bool
   COMPILED_DATA Bool Bool True False
-}

Chars = List Char

Res : Set → Set
Res a = List (a ×' Chars)

ReadS : Set → Set
ReadS a = Chars → Res a

data P (a : Set) : Set where
  Get    : (Char  → P a) → P a
  Look   : (Chars → P a) → P a
  Fail   : P a
  Result : a → P a → P a
  Final  : Res a → P a

final : ∀ {a} → Res a -> P a
final [] = Fail
final r  = Final r

run : ∀ {a} → P a → ReadS a
run (Get f)      (c ∷ s) = run (f c) s
run (Look f)     s       = run (f s) s
run (Result x p) s       = (x ,' s) ∷ run p s
run (Final r)    _       = r
run _            _       = []

monadP : RawMonadPlus P
monadP = record {
    monadZero = record {
        monad = record { return = λ x → Result x Fail ; _>>=_  = _>>=_ }
      ; ∅     = Fail
      }
  ; _∣_ = _∣_
  } where
  mutual
    _>>=_ : ∀ {i j k : ⊤}{A B} → P A → (A → P B) → P B
    Get  f     >>= k = Get  (\ c -> f c >>= k)
    Look f     >>= k = Look (\ s -> f s >>= k)
    Fail       >>= _ = Fail
    Result x p >>= k = k x ∣ (p >>= k)
    Final r    >>= k = final $ r >>=' uncurry' (run ∘ k) where
      open RawMonad Data.List.monad renaming (_>>=_ to _>>='_)
    _∣_   : ∀ {i j : ⊤}{A} → P A → P A → P A
    Get f₁     ∣ Get f₂     = Get (\c -> f₁ c ∣ f₂ c)
    Result x p ∣ q          = Result x (p ∣ q)
    p          ∣ Result x q = Result x (p ∣ q)
    Fail       ∣ p          = p
    p          ∣ Fail       = p
    Final r    ∣ Final t    = Final (r ++ t)
    Final r    ∣ Look f     = Look (\s -> Final (r ++ run (f s) s))
    Final r    ∣ p          = Look (\s -> Final (r ++ run p s))
    Look f     ∣ Final r    = Look (\s -> Final (run (f s) s ++ r))
    p          ∣ Final r    = Look (\s -> Final (run p s ++ r))
    Look f     ∣ Look g     = Look (\s -> f s ∣ g s)
    Look f     ∣ p          = Look (\s -> f s ∣ p)
    p          ∣ Look f     = Look (\s -> p ∣ f s)


data ReadP(a : Set) : Set where
  R : (∀ {b} → (a → P b) → P b) → ReadP a

deR : ∀ {a} → ReadP a → (∀{b} → (a → P b) → P b)
deR (R m) = m


functorR : RawFunctor ReadP
functorR = record {_<$>_ = _<$>_} where
  _<$>_ : ∀ {A B} → (A → B) → ReadP A → ReadP B
  h <$> R f = R $ λ k → f (k ∘ h)

monadR : RawMonadPlus ReadP
monadR = record {
    monadZero = record {
        monad = record { return = λ x → R $ λ k → k x ; _>>=_ = _>>=_}
      ; ∅ = R $ λ _ → Fail
      }
  ; _∣_ = _∣_
  } where
  _>>=_ : ∀ {i j k : ⊤}{A B} → ReadP A → (A → ReadP B) → ReadP B
  R m >>= f = R $ λ k → m $ λ a → deR (f a) k
  
  _∣_ : ∀ {i j k : ⊤}{A} → ReadP A → ReadP A → ReadP A
  R f₁ ∣ R f₂ = R $ λ k → f₁ k ∣' f₂ k where
    open RawMonadPlus monadP renaming (_∣_ to _∣'_)


module MonadsPandR where
  open RawMonadPlus monadP public using ()
    renaming (return to returnP
             ; _>>=_ to _P>>=_
             ; _>>_  to _P>>_
             ; _∣_   to _P|_
             )                      
                           
  open RawMonadPlus monadR public
  

get : ReadP Char
get = R Get

look : ReadP Chars
look = R Look

pfail : ∀ {a} → ReadP a
pfail = RawMonadPlus.∅ monadR

infixr 5 _+++_
_+++_ : ∀ {a} → ReadP a → ReadP a → ReadP a
_+++_ = RawMonadPlus._∣_ monadR

infixr 5 _<++_
_<++_ : ∀ {a} → ReadP a → ReadP a → ReadP a
_<++_ {a} (R f) q = look >>= λ s → probe (f returnP) s 0
  where
  open MonadsPandR
  discard : ℕ → ReadP Unit
  discard 0        = return unit
  discard (suc n)  = get >> discard n

  probe : P a → Chars → ℕ → ReadP a
  probe (Get f)        (c ∷ s) n = probe (f c) s (suc n)
  probe (Look f)       s       n = probe (f s) s n
  probe (Result x s)   _       n = discard n >> R (_P>>=_ (Result x s))
  probe (Final r)      _       _ = R (_P>>=_ (Final r))
  probe _              _       _ = q


gather : ∀{a} → ReadP a -> ReadP (Chars × a)
gather (R m) = R $ λ k → gath id (m (λ a → returnP (λ s → k (s , a))))
  where
  open MonadsPandR
  gath : ∀ {b} → (Chars → Chars) → P (Chars → P b) → P b
  gath     l (Get f)      = Get (λ c -> gath (l ∘ (_∷_ c)) (f c))
  gath     _ Fail         = Fail
  gath     l (Look f)     = Look (λ s -> gath l (f s))
  gath     l (Result k p) = k (l []) P| gath l p
  gath {b} _ (Final _)    = do-not-use-readS_to_P-in-gather!
    where postulate do-not-use-readS_to_P-in-gather! : P b


open MonadsPandR
satisfy : (Char -> Bool) -> ReadP Char
satisfy p = get >>= λ c → if p c then return c else pfail

char : Char → ReadP Char
char c = satisfy (_C==_ c)

eof : ReadP Unit
eof = look >>= λ s → if null s then return unit else pfail

string : String → ReadP String
string this = look >>= λ s → scan (toList this) s
  where
  scan : Chars → Chars → ReadP String
  scan []       _        = return this
  scan (x ∷ xs) (y ∷ ys) = if x C== y then get >> scan xs ys else pfail
  scan _        _        = pfail

munch : (Char → Bool) → ReadP String
munch p = look >>= λ s → fromList <$> scan s
 where
  scan : Chars → ReadP Chars
  scan (c ∷ cs) = if p c then get >> (_∷_ c) <$> scan cs else return []
  scan _        = return []


munch1 : (Char -> Bool) → ReadP String
munch1 p = get >>= λ c → if p c then (_s++_ (fromList (c ∷ [])) <$> munch p)
                                else pfail

choice : ∀ {a} → List (ReadP a) → ReadP a
choice []       = pfail
choice (p ∷ []) = p
choice (p ∷ ps) = p +++ choice ps

private
  primitive
    primIsSpace : Char → Bool

isSpace = primIsSpace

skipSpaces : ReadP Unit
skipSpaces = look >>= skip
  where
  skip : Chars → ReadP Unit
  skip (c ∷ s) = if (isSpace c) then get >> skip s else return unit
  skip _       = return unit


count : ∀ {a} → ℕ -> ReadP a -> ReadP (List a)
count {a} n p = sequence MonadsPandR.monad (replicate n p)


between : ∀ {opn close a} → ReadP opn → ReadP close → ReadP a → ReadP a
between opn close p = opn >> p >>= λ x → close >> return x


option : ∀ {a} → a → ReadP a → ReadP a
option x p = p +++ return x


optional : ∀ {a} → ReadP a -> ReadP Unit
optional p = (p >> return unit) +++ return unit

mutual
  many : ∀ {a} → ReadP a → ReadP (List a)
  many p = return [] +++ many1 p

  many1 : ∀ {a} → ReadP a → ReadP (List a)
  many1 p =  _∷_ <$> p ⊛ many p

skipMany : ∀ {a} → ReadP a -> ReadP Unit
skipMany p = many p >> return unit

skipMany1 : ∀ {a} → ReadP a -> ReadP Unit
skipMany1 p = p >> skipMany p

mutual
  sepBy : ∀ {a sep} → ReadP a -> ReadP sep -> ReadP (List a)
  sepBy p sep = sepBy1 p sep +++ return []

  sepBy1 : ∀ {a sep} → ReadP a -> ReadP sep -> ReadP (List a)
  sepBy1 p sep = _∷_ <$> p ⊛ many (sep >> p)


endBy : ∀ {a sep} → ReadP a -> ReadP sep -> ReadP (List a)
endBy p sep = many (p >>= λ x → sep >> return x)

endBy1 : ∀ {a sep} →  ReadP a -> ReadP sep -> ReadP (List a)
endBy1 p sep = many1 (p >>= λ x → sep >> return x)

mutual
  chainr : ∀ {a} → ReadP a → ReadP (a → a → a) → a → ReadP a
  chainr p op x = chainr1 p op +++ return x

  chainr1 : ∀ {a} → ReadP a → ReadP (a → a → a) → ReadP a
  chainr1 p op = scan
    where scan = p >>= λ x → (op >>= λ f → scan >>= λ y → return (f x y))
                             +++ return x
mutual
  chainl : ∀ {a} → ReadP a → ReadP (a → a → a) → a → ReadP a
  chainl p op x = chainl1 p op +++ return x

  chainl1 : ∀ {a} → ReadP a → ReadP (a → a → a) → ReadP a
  chainl1 p op = p >>= rest
    where rest = λ x → (op >>= λ f → p >>= λ y → rest (f x y)) +++ return x


manyTill : ∀ {a end} → ReadP a -> ReadP end -> ReadP (List a)
manyTill p end = scan
  where scan = (end >> return []) <++ (_∷_ <$> p ⊛ scan)

readP_to_S : ∀ {a} → ReadP a -> ReadS a
readP_to_S {a} (R f) = run (f returnP)

readS_to_P : ∀ {a} → ReadS a → ReadP a
readS_to_P r = R $ λ k → Look $ λ s → final $ r s L>>= uncurry' (run ∘ k)
  where open RawMonad Data.List.monad renaming (_>>=_ to _L>>=_)

{-
import System.IO as IO
main : IO.IO Unit
main = IO.return unit
-}
