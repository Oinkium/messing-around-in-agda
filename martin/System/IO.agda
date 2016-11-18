------------------------------------------------------------------------
-- System.IO
------------------------------------------------------------------------
-- (The sectioning below mostly follows Haskell System.IO documentation)

module System.IO where
{-# IMPORT System.IO #-}

open import IO.Primitive public
open import Category.Monad
open import Data.Unit
open import Data.Char
open import Data.String hiding ( Costring )
open import Foreign.Haskell
open import FFI.Pair
open import Data.Maybe
open import FFI.Int

private Costring = Colist Char

open import Level

IOMonad : RawMonad IO
IOMonad = record { return = return; _>>=_ = _>>=_ }
open RawMonad IOMonad public using (_>>_ ; _<$>_; _⊛_)

------------------------------------------------------------------------
-- Files and Handles

FilePath : Set
FilePath = String

postulate Handle : Set
{-# COMPILED_TYPE Handle System.IO.Handle #-}

postulate stdout : Handle
{-# COMPILED stdout System.IO.stdout #-}

------------------------------------------------------------------------
-- Opening and closing files

-- Opening files

-- Closing files

postulate hClose : Handle -> IO Unit
{-# COMPILED hClose System.IO.hClose #-}

-- ---------------------------------------------------------------------------
-- Buffering modes

data Maybe' (A : Set) : Set where
    just : A → Maybe' A
    nothing : Maybe' A

{-# COMPILED_DATA Maybe' Maybe Just Nothing #-}

data BufferMode : Set where
  NoBuffering    : BufferMode
  LineBuffering  : BufferMode
  BlockBuffering : Maybe' Int → BufferMode

{-# COMPILED_DATA BufferMode System.IO.BufferMode System.IO.NoBuffering System.IO.LineBuffering System.IO.BlockBuffering #-}
 

postulate hSetBuffering : Handle → BufferMode → IO Unit
{-# COMPILED hSetBuffering System.IO.hSetBuffering #-}


------------------------------------------------------------------------
-- Text input and output

-- Text input

-- Text output

postulate hPutStr : Handle -> String -> IO Unit
{-# COMPILED hPutStr System.IO.hPutStr #-}

------------------------------------------------------------------------
-- Temporary Files

postulate openTempFile : FilePath -> String -> IO (FilePath ×' Handle)

{-# COMPILED openTempFile System.IO.openTempFile #-}

-----------------------------------------------------------------------
-- (IO.Primitive.putStrLn is for Costring)

postulate putStrLn' : String -> IO Unit
{-# COMPILED putStrLn' System.IO.putStrLn #-}

postulate getLine' : IO String
{-# COMPILED getLine' System.IO.getLine #-}

{-
open import Foreign.Haskell
open import Data.String hiding ( Costring )
open import Data.Char
open import Foreign.Haskell
Costring = Foreign.Haskell.Colist Char
open import Data.Product
open import Category.Monad
open import FFI.Pair

------------------------------------------------------------------------
-- The IO monad
postulate
  IO : Set -> Set

{-# COMPILED_TYPE IO IO #-}

postulate
  return : {A : Set} -> A -> IO A
  _>>=_  : {A B : Set} -> IO A -> (A -> IO B) -> IO B

{-# COMPILED return (\_ -> return :: a -> IO a) #-}
{-# COMPILED _>>=_  (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}

IOMonad : RawMonad IO
IOMonad = record { return = return; _>>=_ = _>>=_ }
open RawMonad IOMonad public using (_>>_ ; _<$>_; _⊛_)


------------------------------------------------------------------------
-- Files and Handles

FilePath : Set
FilePath = String

postulate Handle : Set
{-# COMPILED_TYPE Handle Handle #-}

------------------------------------------------------------------------
-- Opening and closing files

-- Opening files

-- Closing files

postulate hClose : Handle -> IO Unit
{-# COMPILED hClose hClose #-}

-- Special cases

postulate
  readFile  : FilePath -> IO Costring
  writeFile : FilePath -> Costring -> IO Unit

{-# COMPILED readFile    System.IO.readFile    #-}
{-# COMPILED writeFile   System.IO.writeFile   #-}


------------------------------------------------------------------------
-- Text input and output

-- Text input

-- Text output

postulate hPutStr : Handle -> String -> IO Unit
{-# COMPILED hPutStr System.IO.hPutStr #-}

-- Special cases for standard input and output

postulate
  getContents : IO Costring
  putStr      : Costring -> IO Unit
  putStrLn    : Costring -> IO Unit

{-# COMPILED getContents System.IO.getContents #-}
{-# COMPILED putStr      System.IO.putStr      #-}
{-# COMPILED putStrLn    System.IO.putStrLn    #-}


-}
