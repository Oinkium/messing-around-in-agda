{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Nat.Base where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.TrustMe
import qualified MAlonzo.Code.Relation.Nullary
name6 = "Data.Nat.Base._\8804_"
d6 a0 a1 = ()

data T6 a0 a1 a2 = C10 a0
                 | C18 a0 a1 a2
name20 = "Data.Nat.Base._<_"
d20 = erased
name26 = "Data.Nat.Base._\8805_"
d26 = erased
name32 = "Data.Nat.Base._>_"
d32 = erased
name38 = "Data.Nat.Base._\8816_"
d38 = erased
name44 = "Data.Nat.Base._\8814_"
d44 = erased
name50 = "Data.Nat.Base._\8817_"
d50 = erased
name56 = "Data.Nat.Base._\8815_"
d56 = erased
name64 = "Data.Nat.Base._\8804\8242_"
d64 a0 a1 = ()

data T64 a0 a1 = C68
               | C74 a0 a1
name76 = "Data.Nat.Base._<\8242_"
d76 = erased
name82 = "Data.Nat.Base._\8805\8242_"
d82 = erased
name88 = "Data.Nat.Base._>\8242_"
d88 = erased
name98 = "Data.Nat.Base._\8804\8243_"
d98 a0 a1 = ()

data T98 a0 a1 = C112 a0 a1
name108 = "Data.Nat.Base._\8804\8243_.k"
d108 v0
  = case coe v0 of
        C112 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name110 = "Data.Nat.Base._\8804\8243_.proof"
d110 = erased
name114 = "Data.Nat.Base._<\8243_"
d114 = erased
name120 = "Data.Nat.Base._\8805\8243_"
d120 = erased
name126 = "Data.Nat.Base._>\8243_"
d126 = erased
name136 = "Data.Nat.Base.erase"
d136 v0 v1 v2 = du136 v2
du136 v0 = coe C112 (coe d108 v0) erased
name142 = "Data.Nat.Base.fold"
d142 v0 v1 v2 v3 = du142 v1 v2 v3
du142 v0 v1 v2
  = case coe v2 of
        0 -> coe v0
        _ -> let v3
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v2
                       (1 :: Integer)
               in coe v1 (coe du142 v0 v1 v3)
name162 = "Data.Nat.Base.GeneralisedArithmetic.add"
d162 v0 v1 v2 v3 v4 = du162 v2 v3 v4
du162 v0 v1 v2 = coe du142 v2 v0 v1
name170 = "Data.Nat.Base.GeneralisedArithmetic.mul"
d170 v0 v1 v2 v3 v4 v5 = du170 v1 v3 v4 v5
du170 v0 v1 v2 v3 = coe du142 v0 (coe v1 v3) v2
name180 = "Data.Nat.Base.pred"
d180 v0
  = case coe v0 of
        0 -> 0 :: Integer
        _ -> let v1
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in coe v1
name184 = "Data.Nat.Base._+\8910_"
d184 v0 v1
  = case coe v0 of
        0 -> coe v1
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                 (coe d184 v1 v2)
name192 = "Data.Nat.Base._\8852_"
d192 v0 v1
  = case coe v0 of
        0 -> coe v1
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   0 -> coe v0
                   _ -> let v3
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                  (1 :: Integer)
                          in
                          coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                            (coe d192 v2 v3)
name202 = "Data.Nat.Base._\8851_"
d202 v0 v1
  = case coe v0 of
        0 -> 0 :: Integer
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   0 -> 0 :: Integer
                   _ -> let v3
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                  (1 :: Integer)
                          in
                          coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                            (coe d202 v2 v3)
name212 = "Data.Nat.Base.\8970_/2\8971"
d212 v0
  = case coe v0 of
        0 -> 0 :: Integer
        1 -> 0 :: Integer
        _ -> let v1
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (2 :: Integer)
               in
               coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                 (coe d212 v1)
name216 = "Data.Nat.Base.\8968_/2\8969"
d216 v0
  = coe d212
      (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
         v0)
name220 = "Data.Nat.Base._\8799_"
d220 v0 v1
  = case coe v0 of
        0 -> case coe v1 of
                 0 -> coe MAlonzo.Code.Relation.Nullary.C22 erased
                 _ -> coe MAlonzo.Code.Relation.Nullary.C26 erased
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   0 -> coe MAlonzo.Code.Relation.Nullary.C26 erased
                   _ -> let v3
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                  (1 :: Integer)
                          in
                          let v4 = coe d220 v2 v3 in
                            case coe v4 of
                                MAlonzo.Code.Relation.Nullary.C22 v5 -> coe
                                                                          MAlonzo.Code.Relation.Nullary.C22
                                                                          erased
                                MAlonzo.Code.Relation.Nullary.C26 v5 -> coe
                                                                          MAlonzo.Code.Relation.Nullary.C26
                                                                          (coe
                                                                             MAlonzo.Code.Function.d38
                                                                             erased
                                                                             erased
                                                                             erased
                                                                             erased
                                                                             erased
                                                                             erased
                                                                             (\ v6 -> v5)
                                                                             (\ v6 ->
                                                                                coe
                                                                                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du28
                                                                                  erased))
                                _ -> coe MAlonzo.RTE.mazUnreachableError
name250 = "Data.Nat.Base.\8804-pred"
d250 v0 v1 v2 = du250 v2
du250 v0
  = case coe v0 of
        C18 v1 v2 v3 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name254 = "Data.Nat.Base._\8804?_"
d254 v0 v1
  = case coe v0 of
        0 -> coe MAlonzo.Code.Relation.Nullary.C22 (coe C10 v1)
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   0 -> coe MAlonzo.Code.Relation.Nullary.C26 erased
                   _ -> let v3
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                  (1 :: Integer)
                          in
                          let v4 = coe d254 v2 v3 in
                            case coe v4 of
                                MAlonzo.Code.Relation.Nullary.C22 v5 -> coe
                                                                          MAlonzo.Code.Relation.Nullary.C22
                                                                          (coe C18 v2 v3 v5)
                                MAlonzo.Code.Relation.Nullary.C26 v5 -> coe
                                                                          MAlonzo.Code.Relation.Nullary.C26
                                                                          (coe
                                                                             MAlonzo.Code.Function.d38
                                                                             erased
                                                                             erased
                                                                             erased
                                                                             erased
                                                                             erased
                                                                             erased
                                                                             (\ v6 -> v5)
                                                                             (coe d250 erased
                                                                                erased))
                                _ -> coe MAlonzo.RTE.mazUnreachableError
name278 = "Data.Nat.Base.Ordering"
d278 a0 a1 = ()

data T278 a0 a1 = C284 a0 a1
                | C288 a0
                | C294 a0 a1
name300 = "Data.Nat.Base.compare"
d300 v0 v1
  = case coe v0 of
        0 -> case coe v1 of
                 0 -> coe C288 (0 :: Integer)
                 _ -> let v2
                            = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                (1 :: Integer)
                        in coe C284 (0 :: Integer) v2
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   0 -> coe C294 (0 :: Integer) v2
                   _ -> let v3
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                  (1 :: Integer)
                          in
                          let v4 = coe d300 v2 v3 in
                            case coe v4 of
                                C284 v5 v6 -> coe C284
                                                (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                                                   (1 :: Integer)
                                                   v5)
                                                v6
                                C288 v5 -> coe C288
                                             (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                                                (1 :: Integer)
                                                v5)
                                C294 v5 v6 -> coe C294
                                                (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                                                   (1 :: Integer)
                                                   v5)
                                                v6
                                _ -> coe MAlonzo.RTE.mazUnreachableError
name421 = "Data.Nat.Base..absurdlambda"
d421 = erased
name439 = "Data.Nat.Base..absurdlambda"
d439 = erased
name655 = "Data.Nat.Base..absurdlambda"
d655 = erased