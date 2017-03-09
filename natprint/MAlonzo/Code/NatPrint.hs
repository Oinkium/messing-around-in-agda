{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.NatPrint where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Coinduction
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Coinduction
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.Unit
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.IO
name2 = "NatPrint.\8469"
d2 = ()

data T2 a0 = C4
           | C6 a0
name8 = "NatPrint.toNat"
d8 v0
  = case coe v0 of
        C4 -> 0 :: Integer
        C6 v1 -> coe ((Prelude.+) :: Integer -> Integer -> Integer)
                   (1 :: Integer)
                   (coe d8 v1)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name12 = "NatPrint.printOutNaturalNumbers"
d12 v0 = coe MAlonzo.Code.IO.C28 erased (coe d15 v0) (coe d21 v0)
name15 = "NatPrint._.\9839-0"
d15 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe MAlonzo.Code.IO.d150 (coe v0 (coe C4)))
main = d18
name18 = "NatPrint.main"
d18
  = coe MAlonzo.Code.IO.d42 () erased
      (coe d12
         (coe MAlonzo.Code.Function.d38 erased erased erased erased erased
            erased
            (\ v0 -> MAlonzo.Code.Data.Nat.Show.d22)
            d8))
name21 = "NatPrint._.\9839-1"
d21 v0 v1 = du21 v0
du21 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d12
         (coe MAlonzo.Code.Function.d38 erased erased erased erased erased
            erased
            (\ v1 -> v0)
            (coe C6)))