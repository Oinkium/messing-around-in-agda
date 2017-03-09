{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.On where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
name28 = "Relation.Binary.On._.implies"
d28 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 = du28 v4 v9 v10 v11
du28 v0 v1 v2 v3 = coe v1 (coe v0 v2) (coe v0 v3)
name36 = "Relation.Binary.On._.reflexive"
d36 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du36 v4 v7 v8
du36 v0 v1 v2 = coe v1 (coe v0 v2)
name48 = "Relation.Binary.On._.irreflexive"
d48 = erased
name56 = "Relation.Binary.On._.symmetric"
d56 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du56 v4 v7 v8 v9
du56 v0 v1 v2 v3 = coe v1 (coe v0 v2) (coe v0 v3)
name64 = "Relation.Binary.On._.transitive"
d64 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du64 v4 v7 v8 v9 v10
du64 v0 v1 v2 v3 v4 = coe v1 (coe v0 v2) (coe v0 v3) (coe v0 v4)
name76 = "Relation.Binary.On._.antisymmetric"
d76 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 = du76 v4 v9 v10 v11
du76 v0 v1 v2 v3 = coe v1 (coe v0 v2) (coe v0 v3)
name84 = "Relation.Binary.On._.asymmetric"
d84 = erased
name96 = "Relation.Binary.On._.respects"
d96 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 = du96 v4 v9 v10 v11
du96 v0 v1 v2 v3 = coe v1 (coe v0 v2) (coe v0 v3)
name108 = "Relation.Binary.On._.respects\8322"
d108 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du108 v4 v9
du108 v0 v1
  = coe MAlonzo.Code.Data.Product.C30
      (\ v2 v3 v4 ->
         coe MAlonzo.Code.Data.Product.d26 v1 (coe v0 v2) (coe v0 v3)
           (coe v0 v4))
      (\ v2 v3 v4 ->
         coe MAlonzo.Code.Data.Product.d28 v1 (coe v0 v2) (coe v0 v3)
           (coe v0 v4))
name130 = "Relation.Binary.On._.decidable"
d130 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du130 v4 v7 v8 v9
du130 v0 v1 v2 v3 = coe v1 (coe v0 v2) (coe v0 v3)
name142 = "Relation.Binary.On._.total"
d142 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du142 v4 v7 v8 v9
du142 v0 v1 v2 v3 = coe v1 (coe v0 v2) (coe v0 v3)
name158 = "Relation.Binary.On._.trichotomous"
d158 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 = du158 v4 v9 v10 v11
du158 v0 v1 v2 v3 = coe v1 (coe v0 v2) (coe v0 v3)
name170 = "Relation.Binary.On._.isEquivalence"
d170 v0 v1 v2 v3 v4 v5 v6 v7 = du170 v4 v7
du170 v0 v1
  = coe MAlonzo.Code.Relation.Binary.Core.C605
      (coe d36 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.Core.d516 v1))
      (coe d56 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.Core.d518 v1))
      (coe d64 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.Core.d520 v1))
name198 = "Relation.Binary.On._.isPreorder"
d198 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du198 v4 v9
du198 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C17
      (coe du170 v0 (coe MAlonzo.Code.Relation.Binary.d36 v1))
      (coe d28 erased erased erased erased v0 erased erased erased erased
         (coe MAlonzo.Code.Relation.Binary.d38 v1))
      (coe d64 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.d40 v1))
name236 = "Relation.Binary.On._.isDecEquivalence"
d236 v0 v1 v2 v3 v4 v5 v6 v7 = du236 v4 v7
du236 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C175
      (coe du170 v0 (coe MAlonzo.Code.Relation.Binary.d182 v1))
      (coe d130 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.d184 v1))
name268 = "Relation.Binary.On._.isPartialOrder"
d268 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du268 v4 v9
du268 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C217
      (coe du198 v0 (coe MAlonzo.Code.Relation.Binary.d268 v1))
      (coe d76 erased erased erased erased v0 erased erased erased erased
         (coe MAlonzo.Code.Relation.Binary.d270 v1))
name314 = "Relation.Binary.On._.isDecPartialOrder"
d314 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du314 v4 v9
du314 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C265
      (coe du268 v0 (coe MAlonzo.Code.Relation.Binary.d384 v1))
      (coe d130 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.d386 v1))
      (coe d130 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.d388 v1))
name368 = "Relation.Binary.On._.isStrictPartialOrder"
d368 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du368 v4 v9
du368 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C327
      (coe du170 v0 (coe MAlonzo.Code.Relation.Binary.d570 v1))
      erased
      (coe d64 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.d574 v1))
      (coe du108 v0 (coe MAlonzo.Code.Relation.Binary.d576 v1))
name408 = "Relation.Binary.On._.isTotalOrder"
d408 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du408 v4 v9
du408 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C459
      (coe du268 v0 (coe MAlonzo.Code.Relation.Binary.d842 v1))
      (coe d142 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.d844 v1))
name458 = "Relation.Binary.On._.isDecTotalOrder"
d458 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du458 v4 v9
du458 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C507
      (coe du408 v0 (coe MAlonzo.Code.Relation.Binary.d970 v1))
      (coe d130 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.d972 v1))
      (coe d130 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.d974 v1))
name520 = "Relation.Binary.On._.isStrictTotalOrder"
d520 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du520 v4 v9
du520 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C561
      (coe du170 v0 (coe MAlonzo.Code.Relation.Binary.d1164 v1))
      (coe d64 erased erased erased erased v0 erased erased
         (coe MAlonzo.Code.Relation.Binary.d1166 v1))
      (coe d158 erased erased erased erased v0 erased erased erased
         erased
         (coe MAlonzo.Code.Relation.Binary.d1168 v1))
name578 = "Relation.Binary.On.preorder"
d578 v0 v1 v2 v3 v4 v5 v6 = du578 v4 v5 v6
du578 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.C67 v0
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe du198 v2 (coe MAlonzo.Code.Relation.Binary.d92 v1))
name594 = "Relation.Binary.On.setoid"
d594 v0 v1 v2 v3 v4 v5 = du594 v3 v4 v5
du594 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.C85 v0
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe du170 v2 (coe MAlonzo.Code.Relation.Binary.d136 v1))
name610 = "Relation.Binary.On.decSetoid"
d610 v0 v1 v2 v3 v4 v5 = du610 v3 v4 v5
du610 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.C189 v0
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe du236 v2 (coe MAlonzo.Code.Relation.Binary.d216 v1))
name628 = "Relation.Binary.On.poset"
d628 v0 v1 v2 v3 v4 v5 v6 = du628 v4 v5 v6
du628 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.C235 v0
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe du268 v2 (coe MAlonzo.Code.Relation.Binary.d322 v1))
name646 = "Relation.Binary.On.decPoset"
d646 v0 v1 v2 v3 v4 v5 v6 = du646 v4 v5 v6
du646 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.C289 v0
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe du314 v2 (coe MAlonzo.Code.Relation.Binary.d462 v1))
name664 = "Relation.Binary.On.strictPartialOrder"
d664 v0 v1 v2 v3 v4 v5 v6 = du664 v4 v5 v6
du664 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.C349 v0
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe du368 v2 (coe MAlonzo.Code.Relation.Binary.d616 v1))
name682 = "Relation.Binary.On.totalOrder"
d682 v0 v1 v2 v3 v4 v5 v6 = du682 v4 v5 v6
du682 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.C477 v0
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe du408 v2 (coe MAlonzo.Code.Relation.Binary.d900 v1))
name700 = "Relation.Binary.On.decTotalOrder"
d700 v0 v1 v2 v3 v4 v5 v6 = du700 v4 v5 v6
du700 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.C531 v0
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe du458 v2 (coe MAlonzo.Code.Relation.Binary.d1052 v1))
name718 = "Relation.Binary.On.strictTotalOrder"
d718 v0 v1 v2 v3 v4 v5 v6 = du718 v4 v5 v6
du718 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.C683 v0
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe MAlonzo.Code.Function.d196 erased erased erased erased erased
         erased
         erased
         v2)
      (coe du520 v2 (coe MAlonzo.Code.Relation.Binary.d1226 v1))