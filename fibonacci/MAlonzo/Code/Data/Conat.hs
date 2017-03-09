{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Conat where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Coinduction
import qualified MAlonzo.Code.Coinduction
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
name4 = "Data.Conat.Co\8469"
d4 = ()

data T4 a0 = C6
           | C10 a0
name9 = "Data.Conat._.\9839-0"
d9 v0 = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 (coe d12 v0)
name12 = "Data.Conat.from\8469"
d12 v0
  = case coe v0 of
        0 -> coe C6
        _ -> let v1
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in coe C10 (coe d9 v1)
name16 = "Data.Conat.\8734\8469"
d16 = coe C10 d21
name18 = "Data.Conat._+_"
d18 v0 v1
  = case coe v0 of
        C6 -> coe v1
        C10 v2 -> coe C10 (coe d33 v2 v1)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name21 = "Data.Conat.\9839-1"
d21 = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 d16
name26 = "Data.Conat._\8776_"
d26 a0 a1 = ()

data T26 a0 a1 a2 = C28
                  | C36 a0 a1 a2
name33 = "Data.Conat._.\9839-2"
d33 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d18 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v0) v1)
name38 = "Data.Conat.setoid"
d38
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Relation.Binary.Core.C605 d44 d48 d52)
name44 = "Data.Conat._.refl"
d44 v0
  = case coe v0 of
        C6 -> coe C28
        C10 v1 -> coe C36 v1 v1 (coe d81 v1)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name48 = "Data.Conat._.sym"
d48 v0 v1 v2 = du48 v2
du48 v0
  = case coe v0 of
        C28 -> coe C28
        C36 v1 v2 v3 -> coe C36 v2 v1 (coe d137 v1 v2 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name52 = "Data.Conat._.trans"
d52 v0 v1 v2 v3 v4 = du52 v3 v4
du52 v0 v1
  = case coe v0 of
        C28 -> coe seq v1 (coe C28)
        C36 v2 v3 v4 -> case coe v1 of
                            C36 v5 v6 v7 -> coe C36 v2 v6 (coe d303 v3 v6 v2 v4 v7)
                            _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name81 = "Data.Conat._._.\9839-3"
d81 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d44 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v0))
name137 = "Data.Conat._._.\9839-5"
d137 v0 v1 v2
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe du48 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2))
name303 = "Data.Conat._._.\9839-7"
d303 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe du52 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v3)
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v4))