{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Qhigher_recursive_ordinals where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.IO
name2 = "higher_recursive_ordinals.\8469"
d2 = ()

data T2 a0 = C4
           | C6 a0
name8 = "higher_recursive_ordinals.Ordinal"
d8 = erased
name14 = "higher_recursive_ordinals.zer"
d14 v0 v1 v2 v3 = du14 v1
du14 v0 = coe v0
name24 = "higher_recursive_ordinals.suc"
d24 v0 v1 v2 v3 v4 = du24 v1 v2 v3 v4
du24 v0 v1 v2 v3 = coe v2 (coe v0 v1 v2 v3)
name36 = "higher_recursive_ordinals.lim"
d36 v0 v1 v2 v3 v4 = du36 v1 v2 v3 v4
du36 v0 v1 v2 v3 = coe v3 (\ v4 -> coe v0 v4 v1 v2 v3)
name50 = "higher_recursive_ordinals.FiniteOrdinal"
d50 v0 v1 = du50 v1
du50 v0
  = case coe v0 of
        C4 -> coe d14 erased
        C6 v1 -> coe d24 erased (coe du50 v1)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name56 = "higher_recursive_ordinals.\969"
d56 v0 = du56
du56 = coe d36 erased (coe d50 erased)
name60 = "higher_recursive_ordinals.\969M+N"
d60 v0 v1 v2 = du60 v1 v2
du60 v0 v1
  = let v2
          = case coe v1 of
                C6 v2 -> coe d24 erased (coe du60 v0 v2)
                _ -> coe MAlonzo.RTE.mazUnreachableError
      in
      case coe v0 of
          C4 -> case coe v1 of
                    C4 -> coe d14 erased
                    _ -> coe v2
          C6 v3 -> case coe v1 of
                       C4 -> coe d36 erased (coe d60 erased v3)
                       C6 v4 -> coe d24 erased (coe du60 (coe C6 v3) v4)
                       _ -> coe v2
          _ -> coe v2
name70 = "higher_recursive_ordinals.\969\178"
d70 v0 = du70
du70 = coe d36 erased (\ v0 -> coe du60 v0 (coe C4))
name74 = "higher_recursive_ordinals.NatFunc"
d74 = erased
name76 = "higher_recursive_ordinals.HamiltonZero"
d76 v0 = coe C6 v0
name80 = "higher_recursive_ordinals.HamiltonSucc"
d80 v0 v1 = coe C6 (coe v0 v1)
name86 = "higher_recursive_ordinals.HamiltonLimit"
d86 v0 v1 = coe v0 v1 v1
name92 = "higher_recursive_ordinals.Ordinal'"
d92 = erased
name98 = "higher_recursive_ordinals.zer'"
d98 v0 v1 = du98 v1
du98 v0 = coe v0
name104 = "higher_recursive_ordinals.suc'"
d104 v0 v1 v2 = du104 v1 v2
du104 v0 v1 = coe d24 erased (coe v0 v1)
name112 = "higher_recursive_ordinals.lim'"
d112 v0 v1 v2 = du112 v1 v2
du112 v0 v1 = coe d36 erased (\ v2 -> coe v0 v2 v1)
name120 = "higher_recursive_ordinals.PrintNumber"
d120 v0
  = case coe v0 of
        C4 -> coe Data.Text.pack ""
        C6 v1 -> coe MAlonzo.Code.Agda.Builtin.String.d12 (coe d120 v1)
                   (coe Data.Text.pack "|")
        _ -> coe MAlonzo.RTE.mazUnreachableError
name124 = "higher_recursive_ordinals.Hamilton\969\178"
d124 = coe du70 d76 d80 d86
main = d126
name126 = "higher_recursive_ordinals.main"
d126
  = coe MAlonzo.Code.IO.d42 () erased
      (coe MAlonzo.Code.IO.d150
         (coe d120 (coe d124 (coe C6 (coe C6 (coe C4))))))