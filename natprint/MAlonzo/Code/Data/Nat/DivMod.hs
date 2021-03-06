{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Nat.DivMod where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Properties.Simple
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.TrustMe
import qualified MAlonzo.Code.Relation.Nullary.Decidable
name10 = "Data.Nat.DivMod.DivMod"
d10 a0 a1 = ()

data T10 a0 a1 a2 = C28 a0 a1 a2
name22 = "Data.Nat.DivMod.DivMod.quotient"
d22 v0
  = case coe v0 of
        C28 v1 v2 v3 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name24 = "Data.Nat.DivMod.DivMod.remainder"
d24 v0
  = case coe v0 of
        C28 v1 v2 v3 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name26 = "Data.Nat.DivMod.DivMod.property"
d26 = erased
name36 = "Data.Nat.DivMod._div_"
d36 v0 v1 v2 = du36 v0 v1
du36 v0 v1
  = coe (Prelude.quot :: Integer -> Integer -> Integer) v0 v1
name52 = "Data.Nat.DivMod.mod-lemma"
d52 v0 v1 v2
  = case coe v1 of
        0 -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
               (coe MAlonzo.Code.Data.Nat.d76 v0
                  (coe ((Prelude.+) :: Integer -> Integer -> Integer) v0 v2)
                  (coe ((Prelude.+) :: Integer -> Integer -> Integer) v0 v2)
                  (coe MAlonzo.Code.Data.Nat.Properties.d444 v0 v2)
                  (coe MAlonzo.Code.Data.Nat.d70
                     (coe ((Prelude.+) :: Integer -> Integer -> Integer) v0 v2)))
        _ -> let v3
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in
               case coe v2 of
                   0 -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                          (coe MAlonzo.Code.Data.Nat.d76
                             (coe (Prelude.rem :: Integer -> Integer -> Integer) v3
                                (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                                   v0))
                             v0
                             v0
                             (coe d52 (0 :: Integer) v3 v0)
                             (coe MAlonzo.Code.Data.Nat.d70 v0))
                   _ -> let v4
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v2
                                  (1 :: Integer)
                          in
                          coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du28
                            (coe d52
                               (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                                  v0)
                               v3
                               v4)
name76 = "Data.Nat.DivMod._mod_"
d76 v0 v1
  = let v2
          = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
              (1 :: Integer)
      in
      \ v3 ->
        coe MAlonzo.Code.Data.Fin.du46
          (coe (Prelude.rem :: Integer -> Integer -> Integer) v0 v1)
          (coe MAlonzo.Code.Data.Nat.Base.du136
             (coe MAlonzo.Code.Data.Nat.Properties.du640
                (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                   (coe MAlonzo.Code.Agda.Builtin.Nat.d74 (0 :: Integer)
                      (coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                         (1 :: Integer))
                      v0
                      v2))
                v1))
name94 = "Data.Nat.DivMod.division-lemma"
d94 = erased
name106 = "Data.Nat.DivMod._.s"
d106 v0 v1 v2 = du106 v0 v2
du106 v0 v1
  = coe ((Prelude.+) :: Integer -> Integer -> Integer) v0 v1
name118 = "Data.Nat.DivMod._.s"
d118 v0 v1 v2 = du118 v0
du118 v0 = coe v0
name140 = "Data.Nat.DivMod._.s"
d140 v0 v1 v2 v3 = du140 v0 v3
du140 v0 v1
  = coe ((Prelude.+) :: Integer -> Integer -> Integer)
      (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
         v0)
      v1
name142 = "Data.Nat.DivMod._.s\8242"
d142 v0 v1 v2 v3 = du142 v0 v3
du142 v0 v1
  = coe ((Prelude.+) :: Integer -> Integer -> Integer)
      (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
         v0)
      v1
name160 = "Data.Nat.DivMod._divMod_"
d160 v0 v1 v2 = du160 v0 v1
du160 v0 v1
  = coe C28 (coe du36 v0 v1) (coe d76 v0 v1 erased) erased
name172 = "Data.Nat.DivMod._.lemma"
d172 v0 v1 v2 = du172 v0 v1
du172 v0 v1
  = coe MAlonzo.Code.Data.Nat.Base.C18
      (coe (Prelude.rem :: Integer -> Integer -> Integer) v0
         (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
            v1))
      v1
      (coe d52 (0 :: Integer) v0 v1)
name174 = "Data.Nat.DivMod._.lemma\8242"
d174 v0 v1 v2 = du174 v0 v1
du174 v0 v1
  = coe MAlonzo.Code.Data.Nat.Base.du136
      (coe MAlonzo.Code.Data.Nat.Properties.du640
         (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
            (coe (Prelude.rem :: Integer -> Integer -> Integer) v0
               (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                  v1)))
         (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
            v1))