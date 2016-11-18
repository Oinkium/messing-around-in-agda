module System.Process where

{-# IMPORT System.IO      #-}
{-# IMPORT System.Exit    #-}
{-# IMPORT System.Process #-}

open import Foreign.Haskell
open import Data.Maybe
open import Data.String
open import FFI.Pair
open import System.Exit
open import System.IO

{-# COMPILED_DATA Maybe Maybe Just Nothing #-}
------------------------------------------------------------------------
-- Running sub-process

postulate ProcessHandle : Set
{-# COMPILED_TYPE ProcessHandle ProcessHandle #-}

-- Specific variants of createProcess 

postulate runProcess :  FilePath
                     -> Colist String
                     -> Maybe FilePath
                     -> Maybe (Colist (String ×' String))
                     -> Maybe Handle
                     -> Maybe Handle
                     -> Maybe Handle
                     -> IO ProcessHandle

{-# COMPILED runProcess runProcess #-}

------------------------------------------------------------------------
-- Process Completion

postulate waitForProcess : ProcessHandle -> IO ExitCode

{-# COMPILED waitForProcess waitForProcess  #-}

postulate readProcess :  FilePath
                      -> Colist String
                      -> String
                      -> IO String

{-# COMPILED readProcess readProcess #-}
