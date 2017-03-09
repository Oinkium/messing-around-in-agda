{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Agda.Builtin.IO where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text

type AgdaIO a b = IO b {- OMG hack :: -}
name8 = "Agda.Builtin.IO.IO"
d8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Builtin.IO.IO"