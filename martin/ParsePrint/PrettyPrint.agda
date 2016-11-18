-- Agda rewrite of Haskell Text.PrettyPrint
-- by Yoriyuki Yamagata

{-# OPTIONS --no-termination-check #-}

module ParsePrint.PrettyPrint where

import Data.Nat as N
open import Data.Nat.DivMod
import Data.Fin as Fin
open import Data.Bool hiding (_≟_)
import Data.Char hiding (_≟_)
open Data.Char
import Data.String
open Data.String hiding (_≟_)
import Data.List
open Data.List renaming (_++_ to _+++_)
open import Data.Digit
open import Relation.Binary.Core
open import Relation.Nullary.Core
import Data.Integer as Z


-- helper functions

postulate ℤ : Set
{-# BUILTIN INTEGER ℤ #-}
primitive
-- Integer functions
   primIntegerPlus     : ℤ -> ℤ -> ℤ
   primIntegerMinus    : ℤ -> ℤ -> ℤ
   primIntegerTimes    : ℤ -> ℤ -> ℤ
   primIntegerDiv      : ℤ -> ℤ -> ℤ  -- partial
   primIntegerMod      : ℤ -> ℤ -> ℤ  -- partial
   primIntegerEquality : ℤ -> ℤ -> Bool
   primIntegerLess     : ℤ -> ℤ -> Bool
   primIntegerAbs      : ℤ -> N.ℕ
   primNatToInteger    : N.ℕ -> ℤ
   primShowInteger     : ℤ -> String

private 
  postulate
    undefined : {A : Set} -> A
    impossible : {A : Set} -> A

  toBool : forall {A : Set} -> Dec A -> Bool
  toBool (yes _) = true
  toBool (no _) = false

  spacesN : N.ℕ -> String
  spacesN N.zero = "" 
  spacesN (N.suc n) = " " ++ spacesN n 

--private

private
  +_ : N.ℕ -> ℤ
  +_ = primNatToInteger
  -_ : N.ℕ -> ℤ
  - n = primIntegerMinus (+ 0) (+ n)
  
  _+_ : ℤ -> ℤ -> ℤ
  _+_ = primIntegerPlus
  
  _-_ : ℤ -> ℤ -> ℤ
  _-_ = primIntegerMinus
  
  _*_ : ℤ -> ℤ -> ℤ
  _*_ = primIntegerTimes
  
  _≟_ : ℤ -> ℤ -> Bool
  _≟_ = primIntegerEquality

  Z2prim : Z.ℤ -> ℤ
  Z2prim (Z.-[1+_] n) = - (N.suc n)
  Z2prim (Z.+_     n) = + n

-- (spaces n) generates a list of n spaces
--
-- It should never be called with 'n' < 0, but that can happen for reasons I don't understand
-- Here's a test case:
--	ncat x y = nest 4 $ cat [ x, y ]
--	d1 = foldl1 ncat $ take 50 $ repeat $ char 'a'
--	d2 = parens $  sep [ d1, text "+" , d1 ]
--	main = print d2
-- I (Hugh) don't feel motivated enough to find the Real Bug, so meanwhile we just test for n<=0

private
  spaces : ℤ -> String
  spaces i with primIntegerLess i (+ 0)
  ...         | true             = ""
  ...         | false with primIntegerEquality i (+ 0)
  ...                    | true  = ""
  ...                    | false = " " ++ spaces (primIntegerMinus i (+ 1))

{- Comments from Johannes Waldmann about what the problem might be:

   In the example above, d2 and d1 are deeply nested, but `text "+"' is not, 
   so the layout function tries to "out-dent" it.
   
   when I look at the Doc values that are generated, there are lots of
   Nest constructors with negative arguments.  see this sample output of
   d1 (obtained with hugs, :s -u)
   
   tBeside (TextDetails_Chr 'a') 1 Doc_Empty) (Doc_NilAbove (Doc_Nest
   (-241) (Doc_TextBeside (TextDetails_Chr 'a') 1 Doc_Empty)))))
   (Doc_NilAbove (Doc_Nest (-236) (Doc_TextBeside (TextDetails_Chr 'a') 1
   (Doc_NilAbove (Doc_Nest (-5) (Doc_TextBeside (TextDetails_Chr 'a') 1
   Doc_Empty)))))))) (Doc_NilAbove (Doc_Nest (-231) (Doc_TextBeside
   (TextDetails_Chr 'a') 1 (Doc_NilAbove (Doc_Nest (-5) (Doc_TextBeside
   (TextDetails_Chr 'a') 1 (Doc_NilAbove (Doc_Nest (-5) (Doc_TextBeside
   (TextDetails_Chr 'a') 1 Doc_Empty))))))))))) (Doc_NilAbove (Doc_Nest
-}

  _≤?_ : ℤ -> ℤ -> Bool
  x ≤? y = primIntegerLess x y ∨ primIntegerEquality x y
  
  _<?_ : ℤ -> ℤ -> Bool
  x <? y = primIntegerLess x y
  

-- Division by 2 ... rounding toward 0
  _/2 : ℤ -> ℤ
  x /2 = primIntegerDiv x (primNatToInteger 2)

-- Division ... rounding toward 0
  _/_ : ℤ -> ℤ -> ℤ
  _/_ = primIntegerDiv
-- end

data Mode : Set where
  PageMode : Mode
  ZigZagMode : Mode
  LeftMode : Mode
  OneLineMode : Mode

record Style : Set where 
  field 
    mode : Mode
    lineLength : Z.ℤ
    ribbonsPerLine*1000 : Z.ℤ

style : Style
style = record { lineLength = Z.+_ 100;
                 ribbonsPerLine*1000 = Z.+_ 1500;
                 mode = PageMode }


data TextDetails : Set where
  Chr : Char -> TextDetails
  Str : String -> TextDetails
  PStr : String -> TextDetails

private
  space-text = Chr ' '
  nl-text = Chr '\n'

data Doc : Set where
  Empty : Doc
  NilAbove : Doc -> Doc
  TextBeside : TextDetails -> ℤ -> Doc -> Doc
  Nest : ℤ -> Doc -> Doc
  Union : Doc -> Doc -> Doc
  NoDoc : Doc
  Beside : Doc -> Bool -> Doc -> Doc
  Above : Doc -> Bool -> Doc -> Doc

private
  textBeside-aux : TextDetails -> ℤ -> Doc -> Doc
  textBeside-aux s sl p = TextBeside s sl p

  nest-aux : ℤ -> Doc -> Doc
  nest-aux k p = Nest k p

  union-aux : Doc -> Doc -> Doc
  union-aux p q = Union p q

-- data RDoc
--  = Empty                                -- empty
--  | NilAbove Doc                         -- text "" $$ x
--  | TextBeside TextDetails !Int Doc      -- text s <> x  
--  | Nest !Int Doc                        -- nest k x
--  | Union Doc Doc                        -- ul `union` ur
--  | NoDoc                                -- The empty set of documents
  RDoc = Doc


-- ---------------------------------------------------------------------------
-- @empty@, @text@, @nest@, @union@

empty = Empty

isEmpty : Doc -> Bool
isEmpty Empty = true 
isEmpty _ = false

private
-- mkNest checks for Nest's invariant that it doesn't have an Empty inside it
  mkNest : ℤ -> RDoc -> RDoc
  mkNest k (Nest k1 p) = mkNest (k + k1) p 
  mkNest _ NoDoc = NoDoc 
  mkNest _ Empty = Empty 
  mkNest k p with k ≟ (+ 0)
  ... | true = p
  ... | false = nest-aux k  p 

-- mkUnion checks for an empty document
  mkUnion : RDoc -> RDoc -> RDoc
  mkUnion Empty q = Empty
  mkUnion p q = union-aux p q

-- ---------------------------------------------------------------------------
-- Vertical composition @$$@

  nilAbove-aux : Doc -> Doc
  nilAbove-aux p = NilAbove p

  above-aux : Doc -> Bool -> Doc -> Doc
  above-aux p _ Empty = p
  above-aux Empty _ q = q
  above-aux p g q = Above p g q


infixl 5 _$$_
_$$_ : Doc -> Doc -> Doc
p $$ q = above-aux p false q

infixl 5 _$+$_
_$+$_ : Doc -> Doc -> Doc
p $+$ q = above-aux p true q

vcat = foldr (_$$_)  empty

private
  nilAboveNest : Bool -> ℤ -> RDoc -> RDoc
-- Specfication: aboveNest p g k q = p $g$ (nest k q)
-- Cannot undestand the clause "nilAboveNest _ k _           | k `seq` False = undefined"
  nilAboveNest _ _ Empty = Empty
  nilAboveNest g k (Nest k1 q) = nilAboveNest g (k + k1) q
  nilAboveNest g k q with (not g) ∧ ((+ 0) <? k)
  ... | true = textBeside-aux (Str (spaces k)) k  q 
  ... | false = nilAbove-aux (mkNest k q )
  
  aboveNest : RDoc -> Bool -> ℤ -> RDoc -> RDoc
-- Specfication: aboveNest p g k q = p $g$ (nest k q)
-- aboveNest _                   _ k _ | k `seq` False = undefined ???
  aboveNest NoDoc g n q = NoDoc
  aboveNest (Union p1 p2) g k q = union-aux (aboveNest p1 g k q ) 
                                            (aboveNest p2 g k q )
  aboveNest Empty g k q = mkNest k q 
  aboveNest (Nest k1 p) g k q  = nest-aux k1  (aboveNest p g (k - k1) q)
  aboveNest (TextBeside s sl p) g k q = textBeside-aux s sl rest 
                                        where
                                          k1 = k - sl
                                          f : RDoc -> RDoc
                                          f Empty = nilAboveNest g k1 q 
                                          f _ = aboveNest p g k1 q 
                                          rest = f p
  aboveNest (NilAbove p) g k q = nilAbove-aux (aboveNest p g k q )
  aboveNest (Beside y y' y0) g k q = impossible 
  aboveNest (Above y y' y0) g k q = impossible   -- !FIXME! catch all statement


-- ----------------------------------------------
-- Horizontal composition @<>@

  beside-aux : Doc -> Bool -> Doc -> Doc
  beside-aux p _ Empty = p
  beside-aux Empty _ q = q
  beside-aux p g q = Beside p g q

infixl 6 _<>_
_<>_ : Doc -> Doc -> Doc
p <> q = beside-aux p false q 

infixl 6 _<+>_
_<+>_ : Doc -> Doc -> Doc
p <+> q = beside-aux p true q

hcat = foldr (_<>_)  empty
hsep = foldr (_<+>_) empty

private
-- Specification: text "" <> nilBeside g p 
--              = text "" <g> p
  nilBeside : Bool -> RDoc -> RDoc
  nilBeside g Empty = Empty 
  nilBeside g (Nest _ p) = nilBeside g p 
  nilBeside true p = textBeside-aux space-text (+ 1) p
  nilBeside false p = p 

mutual

  private
    reduceDoc : Doc -> RDoc
    reduceDoc (Beside p g q) = beside p g (reduceDoc q) 
    reduceDoc (Above p g q) = above p g (reduceDoc q) 
    reduceDoc p = p

  above : Doc -> Bool -> RDoc -> RDoc
  above (Above p g1 q1) g2 q2 = above p g1 (above q1 g2 q2) 
  above (Beside p1 g1 q1) g q = aboveNest (reduceDoc (Beside p1 g1 q1)) g (+ 0) (reduceDoc q)
  above p g q = aboveNest p g (+ 0) (reduceDoc q) 

  beside : Doc -> Bool -> RDoc -> RDoc
-- Specification: beside g p q = p <g> q
  beside Empty g q = q 
  beside (NilAbove p) g q = nilAbove-aux (beside p g q )
  beside (TextBeside s sl p) g q = textBeside-aux s  sl  rest  
                                   where rest = f p
                                                where f : Doc -> Doc
                                                      f Empty = nilBeside g q 
                                                      f _ = beside p g q 
  beside (Nest k p) g q = nest-aux k  (beside p g q)
  beside (Union p1 p2) g q = union-aux (beside p1 g q ) (beside p2 g q )
  beside NoDoc g q = NoDoc 
  beside (Beside p1 true q1) true q2 = beside p1 true (beside q1 true q2) 
  beside (Beside p1 true q1) false q2 = beside (reduceDoc (Beside p1 true q1)) false q2 
  beside (Beside p1 false q1) true q2 = beside (reduceDoc (Beside p1 false q1)) true q2 
  beside (Beside p1 false q1) false q2 = beside p1 false (beside q1 false q2) 
  beside (Above p1 g' p2) g q = beside (reduceDoc (Above p1 g' p2)) g q


-- ---------------------------------------------------------------------------
-- Separate, @sep@, Hughes version

-- Specification: sep ps  = oneLiner (hsep ps)
--                         `union`
--                          vcat ps

-- Specification: sep1 g k ys = sep (x : map (nest k) ys)
--                            = oneLiner (x <g> nest k (hsep ys))
--                              `union` x $$ nest k (vcat ys)

-- @oneLiner@ returns the one-line members of the given set of @Doc@s.
oneLiner : Doc -> Doc
oneLiner Empty = Empty 
oneLiner (NilAbove y) = NoDoc 
oneLiner (TextBeside s sl p) = textBeside-aux s sl (oneLiner p)
oneLiner (Nest k p) = nest-aux k (oneLiner p) 
oneLiner (Union p q) = oneLiner p 
oneLiner NoDoc = NoDoc 
oneLiner _ = impossible 

private
  mutual
  
    sepX : Bool -> List Doc -> RDoc
    sepX x [] = empty 
    sepX x (p ∷ ps) = sep1 x (reduceDoc p) (+ 0) ps 

    sep1 : Bool -> RDoc -> ℤ -> List Doc -> RDoc
    sep1 g NoDoc k ys = NoDoc 
    sep1 g (Union p q) k ys = union-aux (sep1 g p k ys)
                                        (aboveNest q false k (reduceDoc (vcat ys)) )
    sep1 g Empty k ys = mkNest k (sepX g ys)
    sep1 g (Nest n p) k ys = nest-aux n (sep1 g p (k - n) ys)
    sep1 g (NilAbove p) k ys = nilAbove-aux (aboveNest p false k (reduceDoc (vcat ys)))
    sep1 g (TextBeside s sl p) k ys = textBeside-aux s sl (sepNB g p (k - sl) ys) 
    sep1 g _ _ _ = impossible -- !FIXME!

-- Specification: sepNB p k ys = sep1 (text "" <> p) k ys
-- Called when we have already found some text in the first item
-- We have to eat up nests
  
    sepNB : Bool -> RDoc -> ℤ -> List Doc -> RDoc
    sepNB g Empty k ys = mkUnion (oneLiner (nilBeside g (reduceDoc rest)) )
                               (nilAboveNest false k (reduceDoc (vcat ys)) )
                        where
                        rest = if g then hsep ys else hcat ys 
    sepNB g (Nest _ p) k ys = sepNB g p k ys 
    sepNB g p k ys = sep1 g p k ys 

sep = sepX true
cat = sepX false

-- ---------------------------------------------------------------------------
-- @fill@

-- Specification: 
--   fill []  = empty
--   fill [p] = p
--   fill (p1:p2:ps) = oneLiner p1 <#> nest (length p1) 
--                                          (fill (oneLiner p2 : ps))
--                     `union`
--                      p1 $$ fill ps

mutual 
  private
  
    fill : Bool -> List Doc -> Doc
    fill g [] = empty 
    fill g (p ∷ ps) = fill1 g (reduceDoc p) (+ 0) ps

    fill1 : Bool -> RDoc -> ℤ -> List Doc -> Doc
    fill1 g NoDoc k ys = NoDoc 
    fill1 g (Union p q) k ys = union-aux (fill1 g p k ys ) 
                                         (aboveNest q false k (fill g ys))
    fill1 g Empty k ys = mkNest k (fill g ys) 
    fill1 g (Nest n p) k ys = nest-aux n (fill1 g p (k - n) ys) 
    fill1 g (NilAbove p) k ys = nilAbove-aux (aboveNest p false k (fill g ys)) 
    fill1 g (TextBeside s sl p) k ys = textBeside-aux s sl (fillNB g p (k - sl) ys )
    fill1 _ _ _ _ = impossible -- !FIXME!
    
    fillNB : Bool -> RDoc -> ℤ -> List Doc -> Doc
    fillNB g (Nest _ p) k ys = fillNB g p k ys 
    fillNB g Empty k [] = Empty 
    fillNB g Empty k (y ∷ ys) = mkUnion (nilBeside g (fill1 g (oneLiner (reduceDoc y)) k1 ys))
                                          (nilAboveNest false k (fill g (y ∷ ys)) )
                                          where
                                            k1 = if g then k - (+ 1) else k 
    fillNB g p k ys = fill1 g p k ys 

fsep = fill true
fcat = fill false

-- ---------------------------------------------------------------------------
-- Selecting the best layout

private
  fits : ℤ         -- Space available
       -> Doc
       -> Bool      -- true if *first line* of Doc fits in space available
  fits n p with n <? (+ 0)
  ... | true = false
  fits n Empty | false = true 
  fits n (NilAbove _) | false = true 
  fits n (TextBeside _ sl p) | false = fits (n - sl) p
  fits n (Nest _ _) | false =  impossible 
  fits n (Union _ _) | false =  impossible 
  fits n NoDoc | false = false 
  fits n (Beside _ _ _) | false =  impossible 
  fits n (Above _ _ _) | false = impossible 
  
  minn : ℤ -> ℤ -> ℤ
  minn x y = if x <? y then x else y

  nicest1 : ℤ -> ℤ -> ℤ -> Doc -> Doc -> Doc
  nicest1 w r sl p q = if fits ((minn w r) - sl) p then p else q 
  
  nicest : ℤ -> ℤ -> Doc -> Doc -> Doc
  nicest w r p q = nicest1 w r (+ 0) p q

  -- @first@ and @nonEmptySet@ are similar to @nicest@ and @fits@, only simpler.
  -- @first@ returns its first argument if it is non-empty, otherwise its second.
  nonEmptySet : RDoc -> Bool
  nonEmptySet Empty = true 
  nonEmptySet (NilAbove y) = true 
  nonEmptySet (TextBeside _ _ p) = nonEmptySet p 
  nonEmptySet (Nest _ p) = nonEmptySet p 
  nonEmptySet (Union p q) = true 
  nonEmptySet NoDoc = false 
  nonEmptySet (Beside _ _ _) = impossible  -- !FIXME!
  nonEmptySet (Above _ _ _) = impossible  -- !FIXME!
  
  first : RDoc -> RDoc -> RDoc
  first p q = if nonEmptySet p then p else q
  
  best : Mode 
         -> ℤ         -- Line length
         -> ℤ         -- Ribbon length 
         -> RDoc 
         -> RDoc      -- No unions in here
  
  best OneLineMode w r p = 
    get p 
    where
      get : RDoc -> RDoc
      get Empty = Empty
      get NoDoc = NoDoc
      get (NilAbove p) = nilAbove-aux (get p) 
      get (TextBeside s sl p) = textBeside-aux s sl (get p) 
      get (Nest k p) = get p 
      get (Union p q) = first (get p) (get q) 
      get _ = impossible  -- !FIXME!
  
  best mode w r p =
    get w p 
    where
      mutual
        get : ℤ                -- (Remaining) width of line
              -> Doc -> Doc
        get w Empty = Empty 
        get w (NilAbove p) = nilAbove-aux (get w p) 
        get w (TextBeside s sl p) = textBeside-aux s sl (get1 w sl p) 
        get w (Nest k p) = nest-aux k (get (w - k) p) 
        get w (Union p q) = nicest w  r  (get w p ) (get w q )
        get w NoDoc = NoDoc 
        get w (Beside _ _ _) = impossible  -- !FIXME!
        get w (Above _ _ _) = impossible   -- !FIXME!
  
        get1 : ℤ         -- (Remaining) width of line
             -> ℤ        -- Amount of first line already eaten up
             -> Doc      -- This is an argument to TextBeside => eat Nests
             -> Doc      -- No unions in here!
        get1 w sl Empty = Empty 
        get1 w sl (NilAbove p) = nilAbove-aux (get (w - sl) p)
        get1 w sl (TextBeside t tl p) = textBeside-aux t  tl  (get1 w (sl + tl) p)
        get1 w sl (Nest k p) = get1 w sl p 
        get1 w sl (Union p q) = nicest1 w r sl (get1 w sl p) (get1 w sl q)
        get1 w sl NoDoc = NoDoc 
        get1 w sl (Beside _ _ _) = impossible   -- !FIXME!
        get1 w sl (Above _ _ _) = impossible    -- !FIXME!

-- ---------------------------------------------------------------------------
-- Some common definition


char : Char -> Doc
char c = textBeside-aux (Chr c) (+ 1) Empty

semi = char ';'
colon = char ':'
comma = char ','
space = char ' '
equals = char '='
lparen = char '('
rparen = char ')'
lbrack = char '['
rbrack = char ']'
lbrace = char '{'
rbrace = char '}'

text : String -> Doc
text s = textBeside-aux (Str s) (+ (length (toList s))) Empty

ptext : String -> Doc
ptext s = textBeside-aux (PStr s) (+ (length (toList s))) Empty

natural : N.ℕ -> Doc
natural n = text (primShowInteger (+ n))

integer : Z.ℤ -> Doc
integer i = cat ((if j <? (+ 0) then [ text "-" ] else [])
                 +++  natural (primIntegerAbs j) ∷ [])
            where 
              j = Z2prim i

private
  indent : ℤ -> String
  indent n = spaces n 

  multi-ch : ℤ -> Char -> String
  multi-ch i ch = fromList (multi-ch' i) where
    multi-ch' : ℤ -> List Char
    multi-ch' i with i ≤? (+ 0)
    ...           | true  = []
    ...           | false = ch ∷ multi-ch' (i - (+ 1))

quotes : Doc -> Doc
quotes p        = char '\'' <> p <> char '\''

doubleQuotes : Doc -> Doc
doubleQuotes p  = char '"' <> p <> char '"'

parens : Doc -> Doc
parens p        = char '(' <> p <> char ')'

brackets : Doc -> Doc
brackets p      = char '[' <> p <> char ']'

braces : Doc -> Doc
braces p        = char '{' <> p <> char '}'

nest : Z.ℤ -> Doc -> RDoc 
nest k p = mkNest (Z2prim k) (reduceDoc p)

hang : Doc -> Z.ℤ -> Doc -> Doc
hang d1 n d2 = sep (d1 ∷ (nest n d2) ∷ [])

punctuate : Doc -> List Doc -> List Doc
punctuate p [] = [] 
punctuate p (d ∷ ds) = go d ds 
                       where
                         go : Doc -> List Doc -> List Doc
                         go d [] = d ∷ []
                         go d (e ∷ es) = (d <> p) ∷ go e es

-- ---------------------------------------------------------------------------
-- Displaying the best layout

private
  easy-display : forall {A} -> TextDetails -> (TextDetails -> A -> A) -> A -> RDoc -> A
  easy-display {A} nl-text txt end doc = 
    lay doc impossible -- !FIXME!
    where
      lay : RDoc -> A -> A
      lay Empty no-doc = end 
      lay (NilAbove p) no-doc = txt nl-text (lay p impossible)
      lay (TextBeside s sl p) no-doc = txt s (lay p no-doc) 
      lay (Nest k p) no-doc = lay p no-doc 
      lay (Union p q) no-doc = {- lay p -} lay q impossible -- Second arg can't be NoDoc  
      lay NoDoc no-doc = no-doc 
      lay (Beside _ _ _) no-doc = impossible  -- !FIXME!
      lay (Above _ _ _) no-doc = impossible   -- !FIXME!
  
  display : forall {A} -> Mode -> ℤ -> ℤ -> (TextDetails -> A -> A) -> A -> RDoc -> A
  display {A} mode page-width ribbon-width txt end doc = 
    lay (+ 0) doc 
    where
      gap-width = page-width - ribbon-width 
      shift = gap-width /2 
      mutual 
    
        lay : ℤ -> RDoc -> A
  --       lay k _            | k `seq` False = undefined
        lay k Empty = end 
        lay k (NilAbove p) = txt nl-text (lay k p) 
        lay k (TextBeside s sl p) =
           f mode 
           where
             f : Mode -> A
             f ZigZagMode =
               if gap-width ≤? k then
                 txt nl-text 
                   (txt (Str (multi-ch shift '/') ) 
                        (txt nl-text 
                             (lay1 (k - shift) s sl p)))
                 else (if k <? (+ 0) then
                 txt nl-text  
                   (txt (Str (multi-ch shift '\\') ) 
                        (txt nl-text
                             (lay1 (k + shift) s sl p )))
                 else
                 lay1 k s sl p  )
             
             f _ = lay1 k s sl p 
           
        lay k (Nest k1 p) = lay (k + k1) p 
        lay k (Union _ _) = impossible 
        lay k NoDoc = impossible 
        lay k (Beside _ _ _) = impossible 
        lay k (Above _ _ _) = impossible 
  
        lay1 : ℤ -> TextDetails -> ℤ -> RDoc -> A
  --        lay1 k _ sl _ | k+sl `seq` False = undefined
        lay1 k s sl p = txt (Str (indent k)) 
                                (txt s  (lay2 (k + sl) p ))
        lay2 : ℤ -> RDoc  -> A
  --        lay2 k _ | k `seq` False = undefined
        lay2 k Empty = end 
        lay2 k (NilAbove p) = txt nl-text (lay k p) 
        lay2 k (TextBeside s sl p) = txt s (lay2 (k + sl) p) 
        lay2 k (Nest _ p) = lay2 k p 
        lay2 _ (Union _ _) = impossible 
        lay2 _ NoDoc = impossible 
        lay2 _ (Beside _ _ _) = impossible 
        lay2 _ (Above _ _ _) = impossible 
    
fullRender : forall {A} -> Mode -> Z.ℤ -> Z.ℤ -> (TextDetails -> A -> A) -> A -> Doc -> A
fullRender OneLineMode _ _ txt end doc = 
  easy-display space-text txt end (reduceDoc doc) 
fullRender LeftMode _ _ txt end doc = 
  easy-display nl-text txt end (reduceDoc doc) 

fullRender mode line-length ribbons-per-line*1000 txt end doc = 
  display mode (Z2prim line-length) ribbon-length txt end best-doc 
  where
    ribbon-length : ℤ
    ribbon-length = ((Z2prim line-length) * (+ 1000)) / (Z2prim ribbons-per-line*1000)

    f : Mode -> ℤ
    f ZigZagMode = + 100000000  -- arbitrary value
    f _ = Z2prim line-length

    hacked-line-length : ℤ
    hacked-line-length = f mode

    best-doc = best mode hacked-line-length ribbon-length (reduceDoc doc) 

private
  string-txt : TextDetails -> String -> String
  string-txt (Chr c) s = fromList (c ∷ []) ++ s
  string-txt (Str s1) s2 = s1 ++ s2 
  string-txt (PStr s1) s2 = s1 ++ s2 

renderStyle : Style -> Doc -> String
renderStyle style doc =
  fullRender (Style.mode style) 
             (Style.lineLength style) 
             (Style.ribbonsPerLine*1000 style ) 
             string-txt  
             ""  
             doc
private
  showDoc : Doc -> String -> String
  showDoc doc rest = fullRender PageMode (Z.+_ 100) (Z.+_ 1500) string-txt rest doc 

render : Doc -> String
render doc = showDoc doc ""

-- -------------------------------------------------------------------------
-- Debugging code
private

  foo : Doc
  foo = sep (text "a" ∷ text "b" ∷ [])
  
  longdoc = sep (text "1234567890123456789012345678901234567890123456789012345678901234567890" ∷ text "1234567890123456789012345678901234567890123456789012345678901234567890" ∷ [])
  
  string = render longdoc
  
  doc' = best PageMode (+ 100) (+ 1500) (reduceDoc longdoc)
  
  string' = display PageMode (+ 100) (+ 1500) string-txt "" doc'

  bar = vcat (text "a" ∷ text "b" ∷ [])

  test-doc = Above
    (Above (TextBeside (Str "do") (+ 2) Empty) false
    (Beside
      (Beside (TextBeside (Str "::") (+ 2) Empty) true
      (Beside
        (Beside (TextBeside (Chr '(') (+ 1) Empty) false
        (Beside
          (Beside (TextBeside (Str "turn") (+ 4) Empty) true
          (TextBeside (Str "==") (+ 2) Empty))
          true (TextBeside (Str "P") (+ 1) Empty)))
        false (TextBeside (Chr ')') (+ 1) Empty)))
      true
      (Above (TextBeside (Str "->") (+ 2) Empty) false
      (Nest (+ 2)
        (TextBeside (Str "printf") (+ 6)
        (TextBeside (Chr '(') (+ 1)
          (TextBeside (Str "Produce\n") (+ 8)
          (TextBeside (Chr ')') (+ 1)
            (TextBeside (Chr ';') (+ 1)
            (NilAbove
              (Nest (- 17)
              (TextBeside (Str "turn") (+ 4)
                (TextBeside (Chr ' ') (+ 1)
                (TextBeside (Chr '=') (+ 1)
                  (TextBeside (Chr ' ') (+ 1)
                  (TextBeside (Str "C") (+ 1) Empty))))))))))))))))
          false (TextBeside (Str "od") (+ 2) Empty)
