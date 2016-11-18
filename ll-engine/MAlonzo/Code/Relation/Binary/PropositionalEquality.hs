{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.PropositionalEquality where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Unit.NonEta
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified
       MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core
import qualified MAlonzo.Code.Relation.Binary.Indexed
import qualified MAlonzo.Code.Relation.Binary.Indexed.Core
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
name26 = "Relation.Binary.PropositionalEquality.subst\8322"
d26 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 = du26 v12
du26 v0 = coe v0
name46 = "Relation.Binary.PropositionalEquality.cong"
d46 = erased
name66 = "Relation.Binary.PropositionalEquality.cong-app"
d66 = erased
name92 = "Relation.Binary.PropositionalEquality.cong\8322"
d92 = erased
name108 = "Relation.Binary.PropositionalEquality.proof-irrelevance"
d108 = erased
name112 = "Relation.Binary.PropositionalEquality.setoid"
d112 v0 v1 = du112 v1
du112 v0
  = coe MAlonzo.Code.Relation.Binary.C85 v0 erased
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
name120 = "Relation.Binary.PropositionalEquality.decSetoid"
d120 v0 v1 v2 = du120 v1 v2
du120 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C189 v0 erased
      (coe MAlonzo.Code.Relation.Binary.C175
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
         v1)
name128 = "Relation.Binary.PropositionalEquality.isPreorder"
d128 v0 v1 = du128
du128
  = coe MAlonzo.Code.Relation.Binary.C17
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
      (\ v0 v1 -> coe MAlonzo.Code.Function.d68 erased erased)
      erased
name132 = "Relation.Binary.PropositionalEquality.preorder"
d132 v0 v1 = du132 v1
du132 v0
  = coe MAlonzo.Code.Relation.Binary.C67 v0 erased erased du128
name144 = "Relation.Binary.PropositionalEquality._\8594-setoid_"
d144 v0 v1 v2 v3 = du144 v3
du144 v0
  = coe MAlonzo.Code.Function.Equality.du206
      (coe MAlonzo.Code.Relation.Binary.Indexed.Core.C253 erased erased
         (coe MAlonzo.Code.Relation.Binary.Indexed.Core.C179
            (\ v1 ->
               coe MAlonzo.Code.Relation.Binary.Core.d516
                 (coe MAlonzo.Code.Relation.Binary.d136 (coe du112 v0)))
            (\ v1 v2 ->
               coe MAlonzo.Code.Relation.Binary.Core.d518
                 (coe MAlonzo.Code.Relation.Binary.d136 (coe du112 v0)))
            (\ v1 v2 v3 ->
               coe MAlonzo.Code.Relation.Binary.Core.d520
                 (coe MAlonzo.Code.Relation.Binary.d136 (coe du112 v0)))))
name162 = "Relation.Binary.PropositionalEquality._\8791_"
d162 = erased
name180 = "Relation.Binary.PropositionalEquality.:\8594-to-\928"
d180 v0 v1 v2 v3 v4 v5 = du180 v4 v5
du180 v0 v1
  = coe MAlonzo.Code.Function.Equality.C15 v1
      (coe d198 erased erased erased erased v0 v1)
name192 = "Relation.Binary.PropositionalEquality._._._\8776_"
d192 = erased
name198 = "Relation.Binary.PropositionalEquality._.cong\8242"
d198 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du198 v4 v5 v6
du198 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.Indexed.Core.d134
      (coe MAlonzo.Code.Relation.Binary.Indexed.Core.d172 v0)
      v2
      (coe v1 v2)
name210 = "Relation.Binary.PropositionalEquality.\8594-to-\10230"
d210 v0 v1 v2 v3 v4 = du210 v4
du210 v0
  = coe d180 erased erased erased erased
      (coe MAlonzo.Code.Relation.Binary.Indexed.Core.C253 erased erased
         (coe MAlonzo.Code.Relation.Binary.Indexed.Core.C179
            (\ v1 ->
               coe MAlonzo.Code.Relation.Binary.Core.d516
                 (coe MAlonzo.Code.Relation.Binary.d136 v0))
            (\ v1 v2 ->
               coe MAlonzo.Code.Relation.Binary.Core.d518
                 (coe MAlonzo.Code.Relation.Binary.d136 v0))
            (\ v1 v2 v3 ->
               coe MAlonzo.Code.Relation.Binary.Core.d520
                 (coe MAlonzo.Code.Relation.Binary.d136 v0))))
name220
  = "Relation.Binary.PropositionalEquality.Deprecated-inspect.Inspect"
d220 a0 a1 a2 = ()

data T220 a0 a1 = C232 a0 a1
name240
  = "Relation.Binary.PropositionalEquality.Deprecated-inspect.inspect"
d240 v0 v1 v2 = du240 v2
du240 v0 = coe C232 v0 erased
name254
  = "Relation.Binary.PropositionalEquality.Deprecated-inspect-on-steroids.Reveal_is_"
d254 a0 a1 a2 a3 = ()

newtype T254 a0 = C266 a0
name282
  = "Relation.Binary.PropositionalEquality.Deprecated-inspect-on-steroids.inspect"
d282 = erased
name304 = "Relation.Binary.PropositionalEquality.Reveal_\183_is_"
d304 a0 a1 a2 a3 a4 a5 a6 = ()

newtype T304 a0 = C324 a0
name322
  = "Relation.Binary.PropositionalEquality.Reveal_\183_is_.eq"
d322 = erased
name340 = "Relation.Binary.PropositionalEquality.inspect"
d340 = erased
name356
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning.begin_"
d356 = erased
name364
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._\8801\10216\10217_"
d364 = erased
name374
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._\8801\10216_\10217_"
d374 = erased
name386
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._\8773\10216_\10217_"
d386 = erased
name394
  = "Relation.Binary.PropositionalEquality.\8801-Reasoning._\8718"
d394 = erased
name400 = "Relation.Binary.PropositionalEquality.Extensionality"
d400 = erased
name426
  = "Relation.Binary.PropositionalEquality.extensionality-for-lower-levels"
d426 = erased
name454
  = "Relation.Binary.PropositionalEquality.\8704-extensionality"
d454 = erased