{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Unit where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Data.Unit.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary
name4 = "Data.Unit._\8799_"
d4 v0 v1 = du4
du4 = coe MAlonzo.Code.Relation.Nullary.C22 erased
name6 = "Data.Unit._\8804?_"
d6 v0 v1 = du6
du6 = coe MAlonzo.Code.Relation.Nullary.C22 erased
name8 = "Data.Unit.total"
d8 v0 v1 = du8
du8 = coe Left erased
name10 = "Data.Unit.preorder"
d10
  = coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du132
      erased
name12 = "Data.Unit.setoid"
d12
  = coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du112
      erased
name14 = "Data.Unit.decTotalOrder"
d14
  = coe MAlonzo.Code.Relation.Binary.C531 erased erased erased
      (coe MAlonzo.Code.Relation.Binary.C507
         (coe MAlonzo.Code.Relation.Binary.C459
            (coe MAlonzo.Code.Relation.Binary.C217
               (coe MAlonzo.Code.Relation.Binary.C17
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
                  erased
                  erased)
               erased)
            d8)
         d4
         d6)
name20 = "Data.Unit._.antisym"
d20 = erased
name28 = "Data.Unit.decSetoid"
d28
  = coe MAlonzo.Code.Relation.Binary.C189 erased erased
      (coe MAlonzo.Code.Relation.Binary.C175
         (coe MAlonzo.Code.Relation.Binary.d36
            (coe MAlonzo.Code.Relation.Binary.d268
               (coe MAlonzo.Code.Relation.Binary.d842
                  (coe MAlonzo.Code.Relation.Binary.d970
                     (coe MAlonzo.Code.Relation.Binary.d1052 d14)))))
         (coe MAlonzo.Code.Relation.Binary.d972
            (coe MAlonzo.Code.Relation.Binary.d1052 d14)))
name30 = "Data.Unit.poset"
d30
  = coe MAlonzo.Code.Relation.Binary.C235 erased erased erased
      (coe MAlonzo.Code.Relation.Binary.d842
         (coe MAlonzo.Code.Relation.Binary.d970
            (coe MAlonzo.Code.Relation.Binary.d1052 d14)))