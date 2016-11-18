module System.Exit where

{-# IMPORT System.Exit #-}

open import FFI.Int
open import FFI.Pair

data ExitCode : Set where
  ExitSuccess : ExitCode
  ExitFailure : Int -> ExitCode
{-# COMPILED_DATA ExitCode ExitCode ExitSuccess ExitFailure #-}
