{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Agda.Builtin.Bool where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
name6 = "Agda.Builtin.Bool.Bool"
d6 = ()

check8 :: Bool
check8 = False

check10 :: Bool
check10 = True

cover6 :: Bool -> ()
cover6 x
  = case x of
        False -> ()
        True -> ()
name8 = "Agda.Builtin.Bool.Bool.false"

d8 :: Bool
d8 = False
name10 = "Agda.Builtin.Bool.Bool.true"

d10 :: Bool
d10 = True