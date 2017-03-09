{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.IO where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Coinduction
import qualified MAlonzo.Code.Coinduction
import qualified MAlonzo.Code.Data.Colist
import qualified MAlonzo.Code.Data.String
import qualified MAlonzo.Code.Data.Unit
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.IO.Primitive
import qualified MAlonzo.Code.Level
name6 = "IO.IO"
d6 a0 a1 = ()

data T6 a0 a1 a2 = C14 a0
                 | C18 a0
                 | C28 a0 a1 a2
                 | C36 a0 a1 a2
name42 = "IO.run"
d42 v0 v1 v2
  = case coe v2 of
        C14 v3 -> coe v3
        C18 v3 -> coe MAlonzo.Code.IO.Primitive.d8 v0 v1 v3
        C28 v3 v4 v5 -> coe MAlonzo.Code.IO.Primitive.d18 v0 v0 v3 v1
                          (coe d42 v0 v3 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v4))
                          (\ v6 ->
                             coe d42 v0 v1
                               (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 (coe v5 v6)))
        C36 v3 v4 v5 -> coe MAlonzo.Code.IO.Primitive.d18 v0 v0 v3 v1
                          (coe d42 v0 v3 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v4))
                          (\ v6 ->
                             coe d42 v0 v1 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v5))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name64 = "IO.sequence"
d64 v0 v1 v2
  = case coe v2 of
        [] -> coe C18 (coe [])
        (:) v3 v4 -> coe C28 v1 (coe du171 v3) (coe d175 v0 v1 erased v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name78 = "IO.sequence\8242"
d78 v0 v1 v2
  = case coe v2 of
        [] -> coe C18 (coe MAlonzo.Code.Level.C20 erased)
        (:) v3 v4 -> coe C36 v1 (coe du471 v3) (coe du475 v0 v1 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name92 = "IO.mapM"
d92 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Function.d38 erased erased erased erased erased
      erased
      (\ v5 -> coe d64 v1 v3)
      (coe MAlonzo.Code.Data.Colist.d150 v0 () v2 erased v4)
name100 = "IO.mapM\8242"
d100 v0 v1 v2
  = coe MAlonzo.Code.Function.d38 erased erased erased erased erased
      erased
      (\ v3 -> coe d78 () v1)
      (coe MAlonzo.Code.Data.Colist.d150 () () v0 erased v2)
name104 = "IO.getContents"
d104 = coe C14 MAlonzo.Code.IO.Primitive.d20
name106 = "IO.readFile"
d106 v0 = coe C14 (coe MAlonzo.Code.IO.Primitive.d22 v0)
name110 = "IO.readFiniteFile"
d110 v0 = coe C14 (coe MAlonzo.Code.IO.Primitive.d32 v0)
name114 = "IO.writeFile\8734"
d114 v0 v1 = coe C36 erased (coe d691 v0 v1) du695
name120 = "IO.writeFile"
d120 v0 v1 = coe d114 v0 (coe MAlonzo.Code.Data.String.d12 v1)
name126 = "IO.appendFile\8734"
d126 v0 v1 = coe C36 erased (coe d707 v0 v1) du711
name132 = "IO.appendFile"
d132 v0 v1 = coe d126 v0 (coe MAlonzo.Code.Data.String.d12 v1)
name138 = "IO.putStr\8734"
d138 v0 = coe C36 erased (coe d721 v0) du725
name142 = "IO.putStr"
d142 v0 = coe d138 (coe MAlonzo.Code.Data.String.d12 v0)
name146 = "IO.putStrLn\8734"
d146 v0 = coe C36 erased (coe d733 v0) du737
name150 = "IO.putStrLn"
d150 v0 = coe d146 (coe MAlonzo.Code.Data.String.d12 v0)
name171 = "IO._.\9839-0"
d171 v0 v1 v2 v3 = du171 v2
du171 v0 = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 v0
name175 = "IO._.\9839-1"
d175 v0 v1 v2 v3 v4 = du175 v0 v1 v3 v4
du175 v0 v1 v2 v3
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe C28 erased (coe du177 v0 v1 v2)
         (coe d181 erased erased erased erased v3))
name177 = "IO._.\9839-2"
d177 v0 v1 v2 v3 v4 = du177 v0 v1 v3
du177 v0 v1 v2
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d64 v0 v1 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2))
name181 = "IO._._.\9839-3"
d181 v0 v1 v2 v3 v4 v5 = du181 v4 v5
du181 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe C18 (coe (:) v0 (coe du183 v1)))
name183 = "IO._._.\9839-5"
d183 v0 v1 v2 v3 v4 v5 = du183 v5
du183 v0 = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 v0
name471 = "IO._.\9839-6"
d471 v0 v1 v2 v3 = du471 v2
du471 v0 = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 v0
name475 = "IO._.\9839-7"
d475 v0 v1 v2 v3 = du475 v0 v1 v3
du475 v0 v1 v2
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe C36 erased (coe du477 v0 v1 v2) du479)
name477 = "IO._.\9839-8"
d477 v0 v1 v2 v3 = du477 v0 v1 v3
du477 v0 v1 v2
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d78 v0 v1 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2))
name479 = "IO._.\9839-9"
d479 v0 v1 v2 v3 = du479
du479
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe C18 (coe MAlonzo.Code.Level.C20 erased))
name691 = "IO._.\9839-10"
d691 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe C14 (coe MAlonzo.Code.IO.Primitive.d24 v0 v1))
name695 = "IO._.\9839-12"
d695 v0 v1 = du695
du695
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 (coe C18 erased)
name707 = "IO._.\9839-13"
d707 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe C14 (coe MAlonzo.Code.IO.Primitive.d26 v0 v1))
name711 = "IO._.\9839-15"
d711 v0 v1 = du711
du711
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 (coe C18 erased)
name721 = "IO._.\9839-16"
d721 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe C14 (coe MAlonzo.Code.IO.Primitive.d28 v0))
name725 = "IO._.\9839-18"
d725 v0 = du725
du725
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 (coe C18 erased)
name733 = "IO._.\9839-19"
d733 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe C14 (coe MAlonzo.Code.IO.Primitive.d30 v0))
name737 = "IO._.\9839-21"
d737 v0 = du737
du737
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 (coe C18 erased)