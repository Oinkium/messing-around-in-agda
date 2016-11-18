{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Function.Equality where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.Indexed
import qualified MAlonzo.Code.Relation.Binary.Indexed.Core
name16 = "Function.Equality.\928"
d16 a0 a1 a2 a3 a4 a5 = ()

data T16 a0 a1 = C15 a0 a1
name38 = "Function.Equality.\928._\10216$\10217_"
d38 v0
  = case coe v0 of
        C15 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name40 = "Function.Equality.\928.cong"
d40 v0
  = case coe v0 of
        C15 v1 v2 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name50 = "Function.Equality._\10230_"
d50 = erased
name62 = "Function.Equality.id"
d62 v0 v1 v2 = du62
du62
  = coe C15 (coe MAlonzo.Code.Function.d68 erased erased)
      (\ v0 v1 -> coe MAlonzo.Code.Function.d68 erased erased)
name82 = "Function.Equality._\8728_"
d82 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du82 v9 v10
du82 v0 v1
  = coe C15
      (coe MAlonzo.Code.Function.d38 erased erased erased erased erased
         erased
         (\ v2 -> coe d38 v0)
         (coe d38 v1))
      (\ v2 v3 ->
         coe MAlonzo.Code.Function.d38 erased erased erased erased erased
           erased
           (\ v4 -> coe d40 v0 (coe d38 v1 v2) (coe d38 v1 v3))
           (coe d40 v1 v2 v3))
name100 = "Function.Equality.const"
d100 v0 v1 v2 v3 v4 v5 v6 = du100 v5 v6
du100 v0 v1
  = coe C15
      (coe MAlonzo.Code.Function.d80 erased erased erased erased v1)
      (\ v2 v3 ->
         coe MAlonzo.Code.Function.d80 erased erased erased erased
           (coe MAlonzo.Code.Relation.Binary.Core.d516
              (coe MAlonzo.Code.Relation.Binary.d136 v0)
              (coe MAlonzo.Code.Function.du80 v1)))
name116 = "Function.Equality.setoid"
d116 v0 v1 v2 v3 v4 v5 = du116 v4 v5
du116 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C85 erased (\ v2 v3 -> ())
      (coe MAlonzo.Code.Relation.Binary.Core.C605 d40
         (\ v2 v3 v4 v5 v6 v7 ->
            coe MAlonzo.Code.Relation.Binary.Indexed.Core.d136
              (coe MAlonzo.Code.Relation.Binary.Indexed.Core.d172 v1)
              v6
              v5
              (coe d38 v2 v6)
              (coe d38 v3 v5)
              (coe v4 v6 v5 (coe du144 v0 v5 v6 v7)))
         (\ v2 v3 v4 v5 v6 v7 v8 v9 ->
            coe MAlonzo.Code.Relation.Binary.Indexed.Core.d138
              (coe MAlonzo.Code.Relation.Binary.Indexed.Core.d172 v1)
              v7
              v7
              v8
              (coe d38 v2 v7)
              (coe d38 v3 v7)
              (coe d38 v4 v8)
              (coe v5 v7 v7 (coe du140 v0 v7))
              (coe v6 v7 v8 v9)))
name128 = "Function.Equality._.From._\8776_"
d128 = erased
name140 = "Function.Equality._.From.refl"
d140 v0 v1 v2 v3 v4 v5 = du140 v4
du140 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Relation.Binary.d136 v0)
name144 = "Function.Equality._.From.sym"
d144 v0 v1 v2 v3 v4 v5 = du144 v4
du144 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Relation.Binary.d136 v0)
name192 = "Function.Equality._\8680_"
d192 v0 v1 v2 v3 v4 v5 = du192 v4 v5
du192 v0 v1
  = coe du116 v0
      (coe MAlonzo.Code.Relation.Binary.Indexed.Core.C253 erased erased
         (coe MAlonzo.Code.Relation.Binary.Indexed.Core.C179
            (\ v2 ->
               coe MAlonzo.Code.Relation.Binary.Core.d516
                 (coe MAlonzo.Code.Relation.Binary.d136 v1))
            (\ v2 v3 ->
               coe MAlonzo.Code.Relation.Binary.Core.d518
                 (coe MAlonzo.Code.Relation.Binary.d136 v1))
            (\ v2 v3 v4 ->
               coe MAlonzo.Code.Relation.Binary.Core.d520
                 (coe MAlonzo.Code.Relation.Binary.d136 v1))))
name206 = "Function.Equality.\8801-setoid"
d206 v0 v1 v2 v3 v4 = du206 v4
du206 v0
  = coe MAlonzo.Code.Relation.Binary.C85 () (\ v1 v2 -> ())
      (coe MAlonzo.Code.Relation.Binary.Core.C605
         (\ v1 v2 ->
            coe MAlonzo.Code.Relation.Binary.Indexed.Core.d134
              (coe MAlonzo.Code.Relation.Binary.Indexed.Core.d172 v0)
              v2
              (coe v1 v2))
         (\ v1 v2 v3 v4 ->
            coe MAlonzo.Code.Relation.Binary.Indexed.Core.d136
              (coe MAlonzo.Code.Relation.Binary.Indexed.Core.d172 v0)
              v4
              v4
              (coe v1 v4)
              (coe v2 v4)
              (coe v3 v4))
         (\ v1 v2 v3 v4 v5 v6 ->
            coe MAlonzo.Code.Relation.Binary.Indexed.Core.d138
              (coe MAlonzo.Code.Relation.Binary.Indexed.Core.d172 v0)
              v6
              v6
              v6
              (coe v1 v6)
              (coe v2 v6)
              (coe v3 v6)
              (coe v4 v6)
              (coe v5 v6)))
name272 = "Function.Equality.flip"
d272 v0 v1 v2 v3 v4 v5 v6 v7 = du272 v3 v7
du272 v0 v1
  = coe C15
      (\ v2 ->
         coe C15 (\ v3 -> coe d38 (coe d38 v1 v3) v2)
           (\ v3 v4 v5 ->
              coe d40 v1 v3 v4 v5 v2 v2
                (coe MAlonzo.Code.Relation.Binary.Core.d516
                   (coe MAlonzo.Code.Relation.Binary.d136 v0)
                   v2)))
      (\ v2 v3 v4 v5 v6 v7 -> coe d40 v1 v5 v6 v7 v2 v3 v4)