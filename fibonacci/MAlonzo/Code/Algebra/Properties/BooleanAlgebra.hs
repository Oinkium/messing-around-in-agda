{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.Properties.BooleanAlgebra where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified
       MAlonzo.Code.Algebra.Properties.DistributiveLattice
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Equivalence
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
name74 = "Algebra.Properties.BooleanAlgebra.DL.poset"
d74 v0 v1 v2 = du74 v2
du74 v0
  = coe MAlonzo.Code.Algebra.Properties.DistributiveLattice.du58
      (coe MAlonzo.Code.Algebra.C355 erased erased
         (coe MAlonzo.Code.Algebra.d1412 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2798
            (coe MAlonzo.Code.Algebra.d1422 v0)))
name76 = "Algebra.Properties.BooleanAlgebra.DL.replace-equality"
d76 v0 v1 v2 = du76 v2
du76 v0
  = coe MAlonzo.Code.Algebra.Properties.DistributiveLattice.d182
      erased
      erased
      (coe MAlonzo.Code.Algebra.C355 erased erased
         (coe MAlonzo.Code.Algebra.d1412 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2798
            (coe MAlonzo.Code.Algebra.d1422 v0)))
name78 = "Algebra.Properties.BooleanAlgebra.DL.\8743-idempotent"
d78 v0 v1 v2 = du78 v2
du78 v0
  = coe MAlonzo.Code.Algebra.Properties.DistributiveLattice.du62
      (coe MAlonzo.Code.Algebra.C355 erased erased
         (coe MAlonzo.Code.Algebra.d1412 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2798
            (coe MAlonzo.Code.Algebra.d1422 v0)))
name80 = "Algebra.Properties.BooleanAlgebra.DL.\8743-\8744-distrib"
d80 v0 v1 v2 = du80 v2
du80 v0
  = coe MAlonzo.Code.Algebra.Properties.DistributiveLattice.du150
      (coe MAlonzo.Code.Algebra.C355 erased erased
         (coe MAlonzo.Code.Algebra.d1412 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2798
            (coe MAlonzo.Code.Algebra.d1422 v0)))
name82
  = "Algebra.Properties.BooleanAlgebra.DL.\8743-\8744-distributiveLattice"
d82 v0 v1 v2 = du82 v2
du82 v0
  = coe MAlonzo.Code.Algebra.Properties.DistributiveLattice.du174
      (coe MAlonzo.Code.Algebra.C355 erased erased
         (coe MAlonzo.Code.Algebra.d1412 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2798
            (coe MAlonzo.Code.Algebra.d1422 v0)))
name84
  = "Algebra.Properties.BooleanAlgebra.DL.\8743-\8744-isDistributiveLattice"
d84 v0 v1 v2 = du84 v2
du84 v0
  = coe MAlonzo.Code.Algebra.Properties.DistributiveLattice.du172
      (coe MAlonzo.Code.Algebra.C355 erased erased
         (coe MAlonzo.Code.Algebra.d1412 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2798
            (coe MAlonzo.Code.Algebra.d1422 v0)))
name86
  = "Algebra.Properties.BooleanAlgebra.DL.\8743-\8744-isLattice"
d86 v0 v1 v2 = du86 v2
du86 v0
  = coe MAlonzo.Code.Algebra.Properties.DistributiveLattice.du64
      (coe MAlonzo.Code.Algebra.C355 erased erased
         (coe MAlonzo.Code.Algebra.d1412 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2798
            (coe MAlonzo.Code.Algebra.d1422 v0)))
name88 = "Algebra.Properties.BooleanAlgebra.DL.\8743-\8744-lattice"
d88 v0 v1 v2 = du88 v2
du88 v0
  = coe MAlonzo.Code.Algebra.Properties.DistributiveLattice.du66
      (coe MAlonzo.Code.Algebra.C355 erased erased
         (coe MAlonzo.Code.Algebra.d1412 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2798
            (coe MAlonzo.Code.Algebra.d1422 v0)))
name90 = "Algebra.Properties.BooleanAlgebra.DL.\8744-idempotent"
d90 v0 v1 v2 = du90 v2
du90 v0
  = coe MAlonzo.Code.Algebra.Properties.DistributiveLattice.du68
      (coe MAlonzo.Code.Algebra.C355 erased erased
         (coe MAlonzo.Code.Algebra.d1412 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2798
            (coe MAlonzo.Code.Algebra.d1422 v0)))
name92 = "Algebra.Properties.BooleanAlgebra.DL.\8744-\8743-distrib"
d92 v0 v1 v2 = du92 v2
du92 v0
  = coe MAlonzo.Code.Algebra.Properties.DistributiveLattice.du136
      (coe MAlonzo.Code.Algebra.C355 erased erased
         (coe MAlonzo.Code.Algebra.d1412 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2798
            (coe MAlonzo.Code.Algebra.d1422 v0)))
name98 = "Algebra.Properties.BooleanAlgebra._._DistributesOver_"
d98 = erased
name116 = "Algebra.Properties.BooleanAlgebra._.Identity"
d116 = erased
name118 = "Algebra.Properties.BooleanAlgebra._.Inverse"
d118 = erased
name134 = "Algebra.Properties.BooleanAlgebra._.Zero"
d134 = erased
name138 = "Algebra.Properties.BooleanAlgebra._.Op\8322"
d138 = erased
name144 = "Algebra.Properties.BooleanAlgebra._._\8718"
d144 v0 v1 v2 = du144 v2
du144 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe MAlonzo.Code.Relation.Binary.C85 erased erased
         (coe MAlonzo.Code.Algebra.Structures.d2482
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))))
name146
  = "Algebra.Properties.BooleanAlgebra._._\8764\10216_\10217_"
d146 v0 v1 v2 = du146 v2
du146 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40
      (coe MAlonzo.Code.Relation.Binary.C85 erased erased
         (coe MAlonzo.Code.Algebra.Structures.d2482
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))))
name160 = "Algebra.Properties.BooleanAlgebra.\8744-complement"
d160 v0 v1 v2 = du160 v2
du160 v0
  = coe MAlonzo.Code.Data.Product.C30 (coe d166 erased erased v0)
      (coe MAlonzo.Code.Algebra.Structures.d2800
         (coe MAlonzo.Code.Algebra.d1422 v0))
name166
  = "Algebra.Properties.BooleanAlgebra._.\8744-complement\737"
d166 v0 v1 v2 v3 = du166 v2 v3
du166 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1416 v0 v1)
            v1)
         (coe MAlonzo.Code.Algebra.d1412 v0 v1
            (coe MAlonzo.Code.Algebra.d1416 v0 v1))
         (coe MAlonzo.Code.Algebra.d1418 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2484
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))
            (coe MAlonzo.Code.Algebra.d1416 v0 v1)
            v1)
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe MAlonzo.Code.Algebra.d1418 v0)
            (coe MAlonzo.Code.Algebra.d1418 v0)
            (coe MAlonzo.Code.Algebra.Structures.d2800
               (coe MAlonzo.Code.Algebra.d1422 v0)
               v1)
            (coe du144 v0 (coe MAlonzo.Code.Algebra.d1418 v0))))
name170 = "Algebra.Properties.BooleanAlgebra.\8743-complement"
d170 v0 v1 v2 = du170 v2
du170 v0
  = coe MAlonzo.Code.Data.Product.C30 (coe d176 erased erased v0)
      (coe MAlonzo.Code.Algebra.Structures.d2802
         (coe MAlonzo.Code.Algebra.d1422 v0))
name176
  = "Algebra.Properties.BooleanAlgebra._.\8743-complement\737"
d176 v0 v1 v2 v3 = du176 v2 v3
du176 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1416 v0 v1)
            v1)
         (coe MAlonzo.Code.Algebra.d1414 v0 v1
            (coe MAlonzo.Code.Algebra.d1416 v0 v1))
         (coe MAlonzo.Code.Algebra.d1420 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2490
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))
            (coe MAlonzo.Code.Algebra.d1416 v0 v1)
            v1)
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe MAlonzo.Code.Algebra.d1420 v0)
            (coe MAlonzo.Code.Algebra.d1420 v0)
            (coe MAlonzo.Code.Algebra.Structures.d2802
               (coe MAlonzo.Code.Algebra.d1422 v0)
               v1)
            (coe du144 v0 (coe MAlonzo.Code.Algebra.d1420 v0))))
name180
  = "Algebra.Properties.BooleanAlgebra.\8743-\8744-isBooleanAlgebra"
d180 v0 v1 v2 = du180 v2
du180 v0
  = coe MAlonzo.Code.Algebra.Structures.C605 (coe du84 v0)
      (coe MAlonzo.Code.Data.Product.d28 (coe du170 v0))
      (coe MAlonzo.Code.Data.Product.d28 (coe du160 v0))
      (coe MAlonzo.Code.Algebra.Structures.d2804
         (coe MAlonzo.Code.Algebra.d1422 v0))
name182
  = "Algebra.Properties.BooleanAlgebra.\8743-\8744-booleanAlgebra"
d182 v0 v1 v2 = du182 v2
du182 v0
  = coe MAlonzo.Code.Algebra.C375 erased erased
      (coe MAlonzo.Code.Algebra.d1414 v0)
      (coe MAlonzo.Code.Algebra.d1412 v0)
      (coe MAlonzo.Code.Algebra.d1416 v0)
      (coe MAlonzo.Code.Algebra.d1420 v0)
      (coe MAlonzo.Code.Algebra.d1418 v0)
      (coe du180 v0)
name184 = "Algebra.Properties.BooleanAlgebra.\8743-identity"
d184 v0 v1 v2 = du184 v2
du184 v0
  = coe MAlonzo.Code.Data.Product.C30
      (\ v1 ->
         coe MAlonzo.Code.Function.du176
           (coe MAlonzo.Code.Algebra.Structures.d2490
              (coe MAlonzo.Code.Algebra.Structures.d2630
                 (coe MAlonzo.Code.Algebra.Structures.d2798
                    (coe MAlonzo.Code.Algebra.d1422 v0)))
              (coe MAlonzo.Code.Algebra.d1418 v0)
              v1)
           (coe MAlonzo.Code.Relation.Binary.Core.d520
              (coe MAlonzo.Code.Algebra.Structures.d2482
                 (coe MAlonzo.Code.Algebra.Structures.d2630
                    (coe MAlonzo.Code.Algebra.Structures.d2798
                       (coe MAlonzo.Code.Algebra.d1422 v0))))
              (coe MAlonzo.Code.Algebra.d1414 v0
                 (coe MAlonzo.Code.Algebra.d1418 v0)
                 v1)
              (coe MAlonzo.Code.Algebra.d1414 v0 v1
                 (coe MAlonzo.Code.Algebra.d1418 v0))
              v1)
           (coe du192 v0 v1))
      (coe d192 erased erased v0)
name192 = "Algebra.Properties.BooleanAlgebra._.x\8743\8868=x"
d192 v0 v1 v2 v3 = du192 v2 v3
du192 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0 v1
            (coe MAlonzo.Code.Algebra.d1418 v0))
         (coe MAlonzo.Code.Algebra.d1414 v0 v1
            (coe MAlonzo.Code.Algebra.d1412 v0 v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
         v1
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               v1)
            (coe MAlonzo.Code.Algebra.Structures.d2494
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               v1
               v1
               (coe MAlonzo.Code.Algebra.d1418 v0)
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1418 v0)
               (coe MAlonzo.Code.Data.Product.d28 (coe du160 v0) v1)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            v1
            v1
            (coe MAlonzo.Code.Data.Product.d28
               (coe MAlonzo.Code.Algebra.Structures.d2496
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe du144 v0 v1)))
name198 = "Algebra.Properties.BooleanAlgebra.\8744-identity"
d198 v0 v1 v2 = du198 v2
du198 v0
  = coe MAlonzo.Code.Data.Product.C30
      (\ v1 ->
         coe MAlonzo.Code.Function.du176
           (coe MAlonzo.Code.Algebra.Structures.d2484
              (coe MAlonzo.Code.Algebra.Structures.d2630
                 (coe MAlonzo.Code.Algebra.Structures.d2798
                    (coe MAlonzo.Code.Algebra.d1422 v0)))
              (coe MAlonzo.Code.Algebra.d1420 v0)
              v1)
           (coe MAlonzo.Code.Relation.Binary.Core.d520
              (coe MAlonzo.Code.Algebra.Structures.d2482
                 (coe MAlonzo.Code.Algebra.Structures.d2630
                    (coe MAlonzo.Code.Algebra.Structures.d2798
                       (coe MAlonzo.Code.Algebra.d1422 v0))))
              (coe MAlonzo.Code.Algebra.d1412 v0
                 (coe MAlonzo.Code.Algebra.d1420 v0)
                 v1)
              (coe MAlonzo.Code.Algebra.d1412 v0 v1
                 (coe MAlonzo.Code.Algebra.d1420 v0))
              v1)
           (coe du206 v0 v1))
      (coe d206 erased erased v0)
name206 = "Algebra.Properties.BooleanAlgebra._.x\8744\8869=x"
d206 v0 v1 v2 v3 = du206 v2 v3
du206 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1412 v0 v1
            (coe MAlonzo.Code.Algebra.d1420 v0))
         (coe MAlonzo.Code.Algebra.d1412 v0 v1
            (coe MAlonzo.Code.Algebra.d1414 v0 v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
         v1
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               v1)
            (coe MAlonzo.Code.Algebra.Structures.d2488
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               v1
               v1
               (coe MAlonzo.Code.Algebra.d1420 v0)
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1420 v0)
               (coe MAlonzo.Code.Data.Product.d28 (coe du170 v0) v1)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v1
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            v1
            v1
            (coe MAlonzo.Code.Data.Product.d26
               (coe MAlonzo.Code.Algebra.Structures.d2496
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe du144 v0 v1)))
name212 = "Algebra.Properties.BooleanAlgebra.\8743-zero"
d212 v0 v1 v2 = du212 v2
du212 v0
  = coe MAlonzo.Code.Data.Product.C30
      (\ v1 ->
         coe MAlonzo.Code.Function.du176
           (coe MAlonzo.Code.Algebra.Structures.d2490
              (coe MAlonzo.Code.Algebra.Structures.d2630
                 (coe MAlonzo.Code.Algebra.Structures.d2798
                    (coe MAlonzo.Code.Algebra.d1422 v0)))
              (coe MAlonzo.Code.Algebra.d1420 v0)
              v1)
           (coe MAlonzo.Code.Relation.Binary.Core.d520
              (coe MAlonzo.Code.Algebra.Structures.d2482
                 (coe MAlonzo.Code.Algebra.Structures.d2630
                    (coe MAlonzo.Code.Algebra.Structures.d2798
                       (coe MAlonzo.Code.Algebra.d1422 v0))))
              (coe MAlonzo.Code.Algebra.d1414 v0
                 (coe MAlonzo.Code.Algebra.d1420 v0)
                 v1)
              (coe MAlonzo.Code.Algebra.d1414 v0 v1
                 (coe MAlonzo.Code.Algebra.d1420 v0))
              (coe MAlonzo.Code.Algebra.d1420 v0))
           (coe du220 v0 v1))
      (coe d220 erased erased v0)
name220 = "Algebra.Properties.BooleanAlgebra._.x\8743\8869=\8869"
d220 v0 v1 v2 v3 = du220 v2 v3
du220 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0 v1
            (coe MAlonzo.Code.Algebra.d1420 v0))
         (coe MAlonzo.Code.Algebra.d1414 v0 v1
            (coe MAlonzo.Code.Algebra.d1414 v0 v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
         (coe MAlonzo.Code.Algebra.d1420 v0)
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               v1)
            (coe MAlonzo.Code.Algebra.Structures.d2494
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               v1
               v1
               (coe MAlonzo.Code.Algebra.d1420 v0)
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1420 v0)
               (coe MAlonzo.Code.Data.Product.d28 (coe du170 v0) v1)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v1)
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe MAlonzo.Code.Algebra.d1420 v0)
            (coe MAlonzo.Code.Function.du158
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1))))
               (coe MAlonzo.Code.Algebra.Structures.d2492
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  v1
                  v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1420 v0)
               (coe MAlonzo.Code.Function.du176 (coe du78 v0 v1)
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v1)
                     v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Relation.Binary.Core.d516
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1420 v0)
                  (coe MAlonzo.Code.Algebra.d1420 v0)
                  (coe MAlonzo.Code.Data.Product.d28 (coe du170 v0) v1)
                  (coe du144 v0 (coe MAlonzo.Code.Algebra.d1420 v0))))))
name226
  = "Algebra.Properties.BooleanAlgebra.\8744-\8743-isCommutativeSemiring"
d226 v0 v1 v2 = du226 v2
du226 v0
  = coe MAlonzo.Code.Algebra.Structures.C313
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.C25
            (coe MAlonzo.Code.Algebra.Structures.d2482
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0))))
            (coe MAlonzo.Code.Algebra.Structures.d2486
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0))))
            (coe MAlonzo.Code.Algebra.Structures.d2488
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))))
         (coe MAlonzo.Code.Data.Product.d26 (coe du198 v0))
         (coe MAlonzo.Code.Algebra.Structures.d2484
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))))
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.C25
            (coe MAlonzo.Code.Algebra.Structures.d2482
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0))))
            (coe MAlonzo.Code.Algebra.Structures.d2492
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0))))
            (coe MAlonzo.Code.Algebra.Structures.d2494
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))))
         (coe MAlonzo.Code.Data.Product.d26 (coe du184 v0))
         (coe MAlonzo.Code.Algebra.Structures.d2490
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))))
      (coe MAlonzo.Code.Data.Product.d28 (coe du80 v0))
      (coe MAlonzo.Code.Data.Product.d26 (coe du212 v0))
name228
  = "Algebra.Properties.BooleanAlgebra.\8744-\8743-commutativeSemiring"
d228 v0 v1 v2 = du228 v2
du228 v0
  = coe MAlonzo.Code.Algebra.C239 erased erased
      (coe MAlonzo.Code.Algebra.d1412 v0)
      (coe MAlonzo.Code.Algebra.d1414 v0)
      (coe MAlonzo.Code.Algebra.d1420 v0)
      (coe MAlonzo.Code.Algebra.d1418 v0)
      (coe du226 v0)
name230 = "Algebra.Properties.BooleanAlgebra.\8744-zero"
d230 v0 v1 v2 = du230 v2
du230 v0
  = coe MAlonzo.Code.Data.Product.C30
      (\ v1 ->
         coe MAlonzo.Code.Function.du176
           (coe MAlonzo.Code.Algebra.Structures.d2484
              (coe MAlonzo.Code.Algebra.Structures.d2630
                 (coe MAlonzo.Code.Algebra.Structures.d2798
                    (coe MAlonzo.Code.Algebra.d1422 v0)))
              (coe MAlonzo.Code.Algebra.d1418 v0)
              v1)
           (coe MAlonzo.Code.Relation.Binary.Core.d520
              (coe MAlonzo.Code.Algebra.Structures.d2482
                 (coe MAlonzo.Code.Algebra.Structures.d2630
                    (coe MAlonzo.Code.Algebra.Structures.d2798
                       (coe MAlonzo.Code.Algebra.d1422 v0))))
              (coe MAlonzo.Code.Algebra.d1412 v0
                 (coe MAlonzo.Code.Algebra.d1418 v0)
                 v1)
              (coe MAlonzo.Code.Algebra.d1412 v0 v1
                 (coe MAlonzo.Code.Algebra.d1418 v0))
              (coe MAlonzo.Code.Algebra.d1418 v0))
           (coe du238 v0 v1))
      (coe d238 erased erased v0)
name238 = "Algebra.Properties.BooleanAlgebra._.x\8744\8868=\8868"
d238 v0 v1 v2 v3 = du238 v2 v3
du238 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1412 v0 v1
            (coe MAlonzo.Code.Algebra.d1418 v0))
         (coe MAlonzo.Code.Algebra.d1412 v0 v1
            (coe MAlonzo.Code.Algebra.d1412 v0 v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
         (coe MAlonzo.Code.Algebra.d1418 v0)
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               v1)
            (coe MAlonzo.Code.Algebra.Structures.d2488
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               v1
               v1
               (coe MAlonzo.Code.Algebra.d1418 v0)
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1418 v0)
               (coe MAlonzo.Code.Data.Product.d28 (coe du160 v0) v1)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v1
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v1)
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe MAlonzo.Code.Algebra.d1418 v0)
            (coe MAlonzo.Code.Function.du158
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1))))
               (coe MAlonzo.Code.Algebra.Structures.d2486
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  v1
                  v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1418 v0)
               (coe MAlonzo.Code.Function.du176 (coe du90 v0 v1)
                  (coe MAlonzo.Code.Algebra.Structures.d2488
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v1)
                     v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Relation.Binary.Core.d516
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1418 v0)
                  (coe MAlonzo.Code.Algebra.d1418 v0)
                  (coe MAlonzo.Code.Data.Product.d28 (coe du160 v0) v1)
                  (coe du144 v0 (coe MAlonzo.Code.Algebra.d1418 v0))))))
name244
  = "Algebra.Properties.BooleanAlgebra.\8743-\8744-isCommutativeSemiring"
d244 v0 v1 v2 = du244 v2
du244 v0
  = coe MAlonzo.Code.Algebra.Structures.C313
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.C25
            (coe MAlonzo.Code.Algebra.Structures.d2482
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0))))
            (coe MAlonzo.Code.Algebra.Structures.d2492
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0))))
            (coe MAlonzo.Code.Algebra.Structures.d2494
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))))
         (coe MAlonzo.Code.Data.Product.d26 (coe du184 v0))
         (coe MAlonzo.Code.Algebra.Structures.d2490
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))))
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.C25
            (coe MAlonzo.Code.Algebra.Structures.d2482
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0))))
            (coe MAlonzo.Code.Algebra.Structures.d2486
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0))))
            (coe MAlonzo.Code.Algebra.Structures.d2488
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))))
         (coe MAlonzo.Code.Data.Product.d26 (coe du198 v0))
         (coe MAlonzo.Code.Algebra.Structures.d2484
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))))
      (coe MAlonzo.Code.Data.Product.d28 (coe du92 v0))
      (coe MAlonzo.Code.Data.Product.d26 (coe du230 v0))
name246
  = "Algebra.Properties.BooleanAlgebra.\8743-\8744-commutativeSemiring"
d246 v0 v1 v2 = du246 v2
du246 v0
  = coe MAlonzo.Code.Algebra.C239 erased erased
      (coe MAlonzo.Code.Algebra.d1414 v0)
      (coe MAlonzo.Code.Algebra.d1412 v0)
      (coe MAlonzo.Code.Algebra.d1418 v0)
      (coe MAlonzo.Code.Algebra.d1420 v0)
      (coe du244 v0)
name252 = "Algebra.Properties.BooleanAlgebra.lemma"
d252 v0 v1 v2 v3 v4 v5 v6 = du252 v2 v3 v4 v5 v6
du252 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe MAlonzo.Code.Algebra.d1416 v0 v1)
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1416 v0 v1)
            (coe MAlonzo.Code.Algebra.d1418 v0))
         v2
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1418 v0))
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe MAlonzo.Code.Data.Product.d28 (coe du184 v0)
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               (coe MAlonzo.Code.Algebra.d1418 v0))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
            v2
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.Structures.d2494
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1418 v0)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1418 v0)
                  v4))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v1)
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2))
               v2
               (coe MAlonzo.Code.Data.Product.d26 (coe du80 v0)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v1
                  v2)
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v1)
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1420 v0)
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2))
                  v2
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Data.Product.d26 (coe du170 v0) v1)
                     (coe MAlonzo.Code.Algebra.Structures.d2488
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v1)
                        (coe MAlonzo.Code.Algebra.d1420 v0)
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2))
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)))
                  (coe du146 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1420 v0)
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2))
                     v2
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Relation.Binary.Core.d518
                           (coe MAlonzo.Code.Algebra.Structures.d2482
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0))))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1420 v0)
                           v3)
                        (coe MAlonzo.Code.Algebra.Structures.d2488
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1420 v0)
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2))
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe MAlonzo.Code.Algebra.Structures.d2482
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0))))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)))
                     (coe du146 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                           v2)
                        v2
                        (coe MAlonzo.Code.Function.du158
                           (coe MAlonzo.Code.Relation.Binary.Core.d518
                              (coe MAlonzo.Code.Algebra.Structures.d2482
                                 (coe MAlonzo.Code.Algebra.Structures.d2630
                                    (coe MAlonzo.Code.Algebra.Structures.d2798
                                       (coe MAlonzo.Code.Algebra.d1422 v0))))
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v1
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                                 v2)
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                                    v2)))
                           (coe MAlonzo.Code.Data.Product.d28 (coe du80 v0) v2 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
                        (coe du146 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v1
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                              v2)
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1418 v0)
                              v2)
                           v2
                           (coe MAlonzo.Code.Function.du176
                              (coe MAlonzo.Code.Data.Product.d28 (coe du160 v0) v1)
                              (coe MAlonzo.Code.Algebra.Structures.d2494
                                 (coe MAlonzo.Code.Algebra.Structures.d2630
                                    (coe MAlonzo.Code.Algebra.Structures.d2798
                                       (coe MAlonzo.Code.Algebra.d1422 v0)))
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v1
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                                 (coe MAlonzo.Code.Algebra.d1418 v0)
                                 v2
                                 v2)
                              (coe MAlonzo.Code.Relation.Binary.Core.d516
                                 (coe MAlonzo.Code.Algebra.Structures.d2482
                                    (coe MAlonzo.Code.Algebra.Structures.d2630
                                       (coe MAlonzo.Code.Algebra.Structures.d2798
                                          (coe MAlonzo.Code.Algebra.d1422 v0))))
                                 v2))
                           (coe du146 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1418 v0)
                                 v2)
                              v2
                              v2
                              (coe MAlonzo.Code.Data.Product.d26 (coe du184 v0) v2)
                              (coe du144 v0 v2)))))))))
name262 = "Algebra.Properties.BooleanAlgebra.\172\8869=\8868"
d262 v0 v1 v2 = du262 v2
du262 v0
  = coe du252 v0 (coe MAlonzo.Code.Algebra.d1420 v0)
      (coe MAlonzo.Code.Algebra.d1418 v0)
      (coe MAlonzo.Code.Data.Product.d28 (coe du184 v0)
         (coe MAlonzo.Code.Algebra.d1420 v0))
      (coe MAlonzo.Code.Data.Product.d28 (coe du230 v0)
         (coe MAlonzo.Code.Algebra.d1420 v0))
name264 = "Algebra.Properties.BooleanAlgebra.\172\8868=\8869"
d264 v0 v1 v2 = du264 v2
du264 v0
  = coe du252 v0 (coe MAlonzo.Code.Algebra.d1418 v0)
      (coe MAlonzo.Code.Algebra.d1420 v0)
      (coe MAlonzo.Code.Data.Product.d28 (coe du212 v0)
         (coe MAlonzo.Code.Algebra.d1418 v0))
      (coe MAlonzo.Code.Data.Product.d28 (coe du198 v0)
         (coe MAlonzo.Code.Algebra.d1418 v0))
name266 = "Algebra.Properties.BooleanAlgebra.\172-involutive"
d266 v0 v1 v2 v3 = du266 v2 v3
du266 v0 v1
  = coe du252 v0 (coe MAlonzo.Code.Algebra.d1416 v0 v1) v1
      (coe MAlonzo.Code.Data.Product.d26 (coe du170 v0) v1)
      (coe MAlonzo.Code.Data.Product.d26 (coe du160 v0) v1)
name274 = "Algebra.Properties.BooleanAlgebra.deMorgan\8321"
d274 v0 v1 v2 v3 v4 = du274 v2 v3 v4
du274 v0 v1 v2
  = coe du252 v0 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
      (coe MAlonzo.Code.Algebra.d1412 v0
         (coe MAlonzo.Code.Algebra.d1416 v0 v1)
         (coe MAlonzo.Code.Algebra.d1416 v0 v2))
      (coe du284 v0 v1 v2)
      (coe du288 v0 v1 v2)
name284 = "Algebra.Properties.BooleanAlgebra._.lem\8321"
d284 v0 v1 v2 v3 v4 = du284 v2 v3 v4
du284 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
         (coe MAlonzo.Code.Algebra.d1420 v0)
         (coe MAlonzo.Code.Data.Product.d26 (coe du80 v0)
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d1416 v0 v1)
            (coe MAlonzo.Code.Algebra.d1416 v0 v2))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
            (coe MAlonzo.Code.Algebra.d1420 v0)
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Algebra.Structures.d2490
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     v1
                     v2)
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Relation.Binary.Core.d516
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
               (coe MAlonzo.Code.Algebra.Structures.d2488
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v2
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
               (coe MAlonzo.Code.Algebra.d1420 v0)
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Algebra.Structures.d2492
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     v2
                     v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.Structures.d2488
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v2 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1414 v0 v2
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
                  (coe MAlonzo.Code.Algebra.Structures.d2492
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     v1
                     v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1414 v0 v2
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2
                        (coe MAlonzo.Code.Algebra.d1420 v0))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1420 v0)))
                  (coe MAlonzo.Code.Algebra.d1420 v0)
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe MAlonzo.Code.Algebra.Structures.d2482
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0))))
                           v2)
                        (coe MAlonzo.Code.Algebra.Structures.d2494
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           v2
                           v2
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                           (coe MAlonzo.Code.Algebra.d1420 v0))
                        (coe MAlonzo.Code.Data.Product.d28 (coe du170 v0) v1))
                     (coe MAlonzo.Code.Algebra.Structures.d2488
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v2
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v2
                           (coe MAlonzo.Code.Algebra.d1420 v0))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1
                           (coe MAlonzo.Code.Algebra.d1414 v0 v2
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1
                           (coe MAlonzo.Code.Algebra.d1420 v0)))
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe MAlonzo.Code.Algebra.Structures.d2482
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0))))
                           v1)
                        (coe MAlonzo.Code.Algebra.Structures.d2494
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           v1
                           v1
                           (coe MAlonzo.Code.Algebra.d1414 v0 v2
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           (coe MAlonzo.Code.Algebra.d1420 v0))
                        (coe MAlonzo.Code.Data.Product.d28 (coe du170 v0) v2)))
                  (coe du146 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v2
                           (coe MAlonzo.Code.Algebra.d1420 v0))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1
                           (coe MAlonzo.Code.Algebra.d1420 v0)))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1420 v0)
                        (coe MAlonzo.Code.Algebra.d1420 v0))
                     (coe MAlonzo.Code.Algebra.d1420 v0)
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Data.Product.d28 (coe du212 v0) v2)
                        (coe MAlonzo.Code.Algebra.Structures.d2488
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v2
                              (coe MAlonzo.Code.Algebra.d1420 v0))
                           (coe MAlonzo.Code.Algebra.d1420 v0)
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1
                              (coe MAlonzo.Code.Algebra.d1420 v0))
                           (coe MAlonzo.Code.Algebra.d1420 v0))
                        (coe MAlonzo.Code.Data.Product.d28 (coe du212 v0) v1))
                     (coe du146 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1420 v0)
                           (coe MAlonzo.Code.Algebra.d1420 v0))
                        (coe MAlonzo.Code.Algebra.d1420 v0)
                        (coe MAlonzo.Code.Algebra.d1420 v0)
                        (coe MAlonzo.Code.Data.Product.d28 (coe du198 v0)
                           (coe MAlonzo.Code.Algebra.d1420 v0))
                        (coe du144 v0 (coe MAlonzo.Code.Algebra.d1420 v0))))))))
name286 = "Algebra.Properties.BooleanAlgebra._.lem\8323"
d286 v0 v1 v2 v3 v4 = du286 v2 v3 v4
du286 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d1416 v0 v1))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe MAlonzo.Code.Algebra.d1412 v0 v2
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1416 v0 v1)
            v2)
         (coe MAlonzo.Code.Data.Product.d28 (coe du92 v0)
            (coe MAlonzo.Code.Algebra.d1416 v0 v1)
            v1
            v2)
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1412 v0 v2
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1418 v0)
               (coe MAlonzo.Code.Algebra.d1412 v0 v2
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               v2)
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Data.Product.d28 (coe du160 v0) v1)
               (coe MAlonzo.Code.Algebra.Structures.d2494
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1418 v0)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1418 v0)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
               (coe MAlonzo.Code.Algebra.d1412 v0 v2
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v2)
               (coe MAlonzo.Code.Data.Product.d26 (coe du184 v0)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.Structures.d2484
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe du144 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2))))))
name288 = "Algebra.Properties.BooleanAlgebra._.lem\8322"
d288 v0 v1 v2 v3 v4 = du288 v2 v3 v4
du288 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe MAlonzo.Code.Algebra.d1416 v0 v2))
         (coe MAlonzo.Code.Algebra.d1418 v0)
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
            (coe MAlonzo.Code.Algebra.Structures.d2486
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1416 v0 v2))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v2)
               (coe MAlonzo.Code.Algebra.d1416 v0 v2))
            (coe MAlonzo.Code.Algebra.d1418 v0)
            (coe MAlonzo.Code.Function.du176 (coe du286 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Structures.d2488
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               (coe MAlonzo.Code.Algebra.d1418 v0)
               (coe MAlonzo.Code.Algebra.Structures.d2486
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v2
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1418 v0))
                  (coe MAlonzo.Code.Algebra.d1418 v0)
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                     (coe MAlonzo.Code.Algebra.Structures.d2488
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1412 v0 v2
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1418 v0))
                     (coe MAlonzo.Code.Data.Product.d28 (coe du160 v0) v2))
                  (coe du146 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1418 v0))
                     (coe MAlonzo.Code.Algebra.d1418 v0)
                     (coe MAlonzo.Code.Algebra.d1418 v0)
                     (coe MAlonzo.Code.Data.Product.d28 (coe du230 v0)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                     (coe du144 v0 (coe MAlonzo.Code.Algebra.d1418 v0)))))))
name294 = "Algebra.Properties.BooleanAlgebra.deMorgan\8322"
d294 v0 v1 v2 v3 v4 = du294 v2 v3 v4
du294 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1416 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
         (coe MAlonzo.Code.Algebra.d1416 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1416 v0 v1)
            (coe MAlonzo.Code.Algebra.d1416 v0 v2))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Algebra.Structures.d2804
               (coe MAlonzo.Code.Algebra.d1422 v0)
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  v1
                  (coe du266 v0 v1))
               (coe MAlonzo.Code.Algebra.Structures.d2488
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  v1
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  v2
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  v2
                  (coe du266 v0 v2))))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               (coe MAlonzo.Code.Algebra.d1416 v0 v2))
            (coe MAlonzo.Code.Function.du158
               (coe MAlonzo.Code.Algebra.Structures.d2804
                  (coe MAlonzo.Code.Algebra.d1422 v0)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
                  (coe du274 v0 (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe du266 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               (coe du144 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))))))
name306 = "Algebra.Properties.BooleanAlgebra.replace-equality"
d306 v0 v1 v2 v3 v4 = du306 v2 v3 v4
du306 v0 v1 v2
  = coe MAlonzo.Code.Algebra.C375 erased v1
      (coe MAlonzo.Code.Algebra.d1412 v0)
      (coe MAlonzo.Code.Algebra.d1414 v0)
      (coe MAlonzo.Code.Algebra.d1416 v0)
      (coe MAlonzo.Code.Algebra.d1418 v0)
      (coe MAlonzo.Code.Algebra.d1420 v0)
      (coe MAlonzo.Code.Algebra.Structures.C605
         (coe MAlonzo.Code.Algebra.d1344 (coe du76 v0 v1 v2))
         (\ v3 ->
            coe MAlonzo.Code.Function.Equality.d38
              (coe MAlonzo.Code.Function.Equivalence.d34
                 (coe v2
                    (coe MAlonzo.Code.Algebra.d1412 v0 v3
                       (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                    (coe MAlonzo.Code.Algebra.d1418 v0)))
              (coe MAlonzo.Code.Algebra.Structures.d2800
                 (coe MAlonzo.Code.Algebra.d1422 v0)
                 v3))
         (\ v3 ->
            coe MAlonzo.Code.Function.Equality.d38
              (coe MAlonzo.Code.Function.Equivalence.d34
                 (coe v2
                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                       (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                    (coe MAlonzo.Code.Algebra.d1420 v0)))
              (coe MAlonzo.Code.Algebra.Structures.d2802
                 (coe MAlonzo.Code.Algebra.d1422 v0)
                 v3))
         (\ v3 v4 v5 ->
            coe MAlonzo.Code.Function.Equality.d38
              (coe MAlonzo.Code.Function.Equivalence.d34
                 (coe v2 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                    (coe MAlonzo.Code.Algebra.d1416 v0 v4)))
              (coe MAlonzo.Code.Algebra.Structures.d2804
                 (coe MAlonzo.Code.Algebra.d1422 v0)
                 v3
                 v4
                 (coe MAlonzo.Code.Function.Equality.d38
                    (coe MAlonzo.Code.Function.Equivalence.d36 (coe v2 v3 v4))
                    v5))))
name322 = "Algebra.Properties.BooleanAlgebra._.E.from"
d322 v0 v1 v2 v3 v4 = du322 v2 v3 v4
du322 v0 v1 v2
  = coe MAlonzo.Code.Function.Equivalence.d36 (coe v0 v1 v2)
name324 = "Algebra.Properties.BooleanAlgebra._.E.to"
d324 v0 v1 v2 v3 v4 = du324 v2 v3 v4
du324 v0 v1 v2
  = coe MAlonzo.Code.Function.Equivalence.d34 (coe v0 v1 v2)
name342 = "Algebra.Properties.BooleanAlgebra.XorRing._\8853_"
d342 v0 v1 v2 = du342 v1
du342 v0 = coe v0
name352 = "Algebra.Properties.BooleanAlgebra.XorRing.helper"
d352 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du352 v2 v5 v6 v7 v8 v9 v10
du352 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Function.du176 v5
      (coe MAlonzo.Code.Algebra.Structures.d2494
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.Structures.d2798
               (coe MAlonzo.Code.Algebra.d1422 v0)))
         v1
         v2
         (coe MAlonzo.Code.Algebra.d1416 v0 v3)
         (coe MAlonzo.Code.Algebra.d1416 v0 v4))
      (coe MAlonzo.Code.Algebra.Structures.d2804
         (coe MAlonzo.Code.Algebra.d1422 v0)
         v3
         v4
         v6)
name362
  = "Algebra.Properties.BooleanAlgebra.XorRing.\8853-\172-distrib\737"
d362 v0 v1 v2 v3 v4 v5 v6 = du362 v2 v3 v4 v5 v6
du362 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe MAlonzo.Code.Algebra.d1416 v0 (coe v1 v3 v4))
         (coe MAlonzo.Code.Algebra.d1416 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4))))
         (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Algebra.Structures.d2804
               (coe MAlonzo.Code.Algebra.d1422 v0)
               (coe v1 v3 v4)
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4))))
            (coe v2 v3 v4))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4))))
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v4
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))))
            (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
            (coe MAlonzo.Code.Algebra.Structures.d2804
               (coe MAlonzo.Code.Algebra.d1422 v0)
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v4
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4))))
               (coe MAlonzo.Code.Data.Product.d28 (coe du80 v0)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4))
                  v3
                  v4))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v4
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))))
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v4
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)))))
               (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Algebra.Structures.d2804
                     (coe MAlonzo.Code.Algebra.d1422 v0)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4))))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)))))
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4))))
                     (coe MAlonzo.Code.Algebra.Structures.d2488
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3))))
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe MAlonzo.Code.Algebra.Structures.d2482
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0))))
                           v4)
                        (coe MAlonzo.Code.Algebra.Structures.d2494
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           v4
                           v4
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4))
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)))
                        (coe MAlonzo.Code.Algebra.Structures.d2804
                           (coe MAlonzo.Code.Algebra.d1422 v0)
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)
                           (coe MAlonzo.Code.Algebra.Structures.d2490
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0)))
                              v3
                              v4)))))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)))))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3
                           (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
                  (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
                  (coe MAlonzo.Code.Function.du158
                     (coe MAlonzo.Code.Algebra.Structures.d2804
                        (coe MAlonzo.Code.Algebra.d1422 v0)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3))))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
                     (coe MAlonzo.Code.Function.du176 (coe du376 v0 v3 v4)
                        (coe MAlonzo.Code.Algebra.Structures.d2488
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                        (coe du376 v0 v4 v3)))
                  (coe du146 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4)))
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
                     (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
                     (coe du294 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3
                           (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                     (coe du146 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4)))
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v4
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4)))
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v4
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
                        (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
                        (coe MAlonzo.Code.Function.du176
                           (coe du274 v0 v3 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                           (coe MAlonzo.Code.Algebra.Structures.d2494
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0)))
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v4)))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 (coe MAlonzo.Code.Algebra.d1416 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v4)))
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v4
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v4
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
                           (coe MAlonzo.Code.Relation.Binary.Core.d516
                              (coe MAlonzo.Code.Algebra.Structures.d2482
                                 (coe MAlonzo.Code.Algebra.Structures.d2630
                                    (coe MAlonzo.Code.Algebra.Structures.d2798
                                       (coe MAlonzo.Code.Algebra.d1422 v0))))
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v4
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)))))
                        (coe du146 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 (coe MAlonzo.Code.Algebra.d1416 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v4)))
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v4
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 v4)
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    v4)))
                           (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
                           (coe du352 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 (coe MAlonzo.Code.Algebra.d1416 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v4)))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 v4)
                              (coe MAlonzo.Code.Algebra.d1414 v0 v4
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 v4)
                              (coe MAlonzo.Code.Function.du176
                                 (coe MAlonzo.Code.Relation.Binary.Core.d516
                                    (coe MAlonzo.Code.Algebra.Structures.d2482
                                       (coe MAlonzo.Code.Algebra.Structures.d2630
                                          (coe MAlonzo.Code.Algebra.Structures.d2798
                                             (coe MAlonzo.Code.Algebra.d1422 v0))))
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                                 (coe MAlonzo.Code.Algebra.Structures.d2488
                                    (coe MAlonzo.Code.Algebra.Structures.d2630
                                       (coe MAlonzo.Code.Algebra.Structures.d2798
                                          (coe MAlonzo.Code.Algebra.d1422 v0)))
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                    v4)
                                 (coe du266 v0 v4))
                              (coe MAlonzo.Code.Algebra.Structures.d2490
                                 (coe MAlonzo.Code.Algebra.Structures.d2630
                                    (coe MAlonzo.Code.Algebra.Structures.d2798
                                       (coe MAlonzo.Code.Algebra.d1422 v0)))
                                 v4
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                           (coe du146 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    v4)
                                 (coe MAlonzo.Code.Algebra.d1416 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       v4)))
                              (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
                              (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
                              (coe MAlonzo.Code.Function.du158
                                 (coe MAlonzo.Code.Relation.Binary.Core.d518
                                    (coe MAlonzo.Code.Algebra.Structures.d2482
                                       (coe MAlonzo.Code.Algebra.Structures.d2630
                                          (coe MAlonzo.Code.Algebra.Structures.d2798
                                             (coe MAlonzo.Code.Algebra.d1422 v0))))
                                    (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                          v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                             v4))))
                                 (coe v2 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4))
                              (coe du144 v0
                                 (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4))))))))))
name376 = "Algebra.Properties.BooleanAlgebra.XorRing._.lem"
d376 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du376 v2 v7 v8
du376 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0 v1
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
         (coe MAlonzo.Code.Algebra.d1414 v0 v1
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
         (coe MAlonzo.Code.Algebra.d1414 v0 v1
            (coe MAlonzo.Code.Algebra.d1416 v0 v2))
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               v1)
            (coe MAlonzo.Code.Algebra.Structures.d2494
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               v1
               v1
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
            (coe du274 v0 v1 v2))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
            (coe MAlonzo.Code.Algebra.d1414 v0 v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v2))
            (coe MAlonzo.Code.Data.Product.d26 (coe du80 v0) v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               (coe MAlonzo.Code.Algebra.d1416 v0 v2))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1420 v0)
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Data.Product.d28 (coe du170 v0) v1)
                  (coe MAlonzo.Code.Algebra.Structures.d2488
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                     (coe MAlonzo.Code.Algebra.d1420 v0)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                  (coe MAlonzo.Code.Relation.Binary.Core.d516
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1420 v0)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Data.Product.d26 (coe du198 v0)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                  (coe du144 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)))))))
name382 = "Algebra.Properties.BooleanAlgebra.XorRing.\8853-comm"
d382 v0 v1 v2 v3 v4 v5 v6 = du382 v2 v3 v4 v5 v6
du382 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe v1 v3 v4)
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
         (coe v1 v4 v3)
         (coe v2 v3 v4)
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v4 v3)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)))
            (coe v1 v4 v3)
            (coe du352 v0 (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.d1412 v0 v4 v3)
               (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)
               (coe MAlonzo.Code.Algebra.Structures.d2484
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  v3
                  v4)
               (coe MAlonzo.Code.Algebra.Structures.d2490
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  v3
                  v4))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v4 v3)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)))
               (coe v1 v4 v3)
               (coe v1 v4 v3)
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe v1 v4 v3)
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v4 v3)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3))))
                  (coe v2 v4 v3))
               (coe du144 v0 (coe v1 v4 v3)))))
name392
  = "Algebra.Properties.BooleanAlgebra.XorRing.\8853-\172-distrib\691"
d392 v0 v1 v2 v3 v4 v5 v6 = du392 v2 v3 v4 v5 v6
du392 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe MAlonzo.Code.Algebra.d1416 v0 (coe v1 v3 v4))
         (coe MAlonzo.Code.Algebra.d1416 v0 (coe v1 v4 v3))
         (coe v1 v3 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Algebra.Structures.d2804
               (coe MAlonzo.Code.Algebra.d1422 v0)
               (coe v1 v3 v4)
               (coe v1 v4 v3))
            (coe du382 v0 v1 v2 v3 v4))
         (coe du146 v0 (coe MAlonzo.Code.Algebra.d1416 v0 (coe v1 v4 v3))
            (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v4) v3)
            (coe v1 v3 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
            (coe du362 v0 v1 v2 v4 v3)
            (coe du146 v0 (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v4) v3)
               (coe v1 v3 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
               (coe v1 v3 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
               (coe du382 v0 v1 v2 (coe MAlonzo.Code.Algebra.d1416 v0 v4) v3)
               (coe du144 v0
                  (coe v1 v3 (coe MAlonzo.Code.Algebra.d1416 v0 v4))))))
name402
  = "Algebra.Properties.BooleanAlgebra.XorRing.\8853-annihilates-\172"
d402 v0 v1 v2 v3 v4 v5 v6 = du402 v2 v3 v4 v5 v6
du402 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe v1 v3 v4)
         (coe MAlonzo.Code.Algebra.d1416 v0
            (coe MAlonzo.Code.Algebra.d1416 v0 (coe v1 v3 v4)))
         (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
            (coe MAlonzo.Code.Algebra.d1416 v0 v4))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 (coe v1 v3 v4)))
               (coe v1 v3 v4))
            (coe du266 v0 (coe v1 v3 v4)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 (coe v1 v3 v4)))
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4))
            (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
               (coe MAlonzo.Code.Algebra.d1416 v0 v4))
            (coe MAlonzo.Code.Function.du158
               (coe MAlonzo.Code.Algebra.Structures.d2804
                  (coe MAlonzo.Code.Algebra.d1422 v0)
                  (coe MAlonzo.Code.Algebra.d1416 v0 (coe v1 v3 v4))
                  (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4))
               (coe du362 v0 v1 v2 v3 v4))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4))
               (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v4))
               (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v4))
               (coe du392 v0 v1 v2 (coe MAlonzo.Code.Algebra.d1416 v0 v3) v4)
               (coe du144 v0
                  (coe v1 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v4))))))
name408 = "Algebra.Properties.BooleanAlgebra.XorRing.\8853-cong"
d408 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du408 v2 v3 v4 v5 v6 v7 v8 v9 v10
du408 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe v1 v3 v5)
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v3 v5)
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5)))
         (coe v1 v4 v6)
         (coe v2 v3 v5)
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v3 v5)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v4 v6)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v4 v6)))
            (coe v1 v4 v6)
            (coe du352 v0 (coe MAlonzo.Code.Algebra.d1412 v0 v3 v5)
               (coe MAlonzo.Code.Algebra.d1412 v0 v4 v6)
               (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5)
               (coe MAlonzo.Code.Algebra.d1414 v0 v4 v6)
               (coe MAlonzo.Code.Function.du176 v7
                  (coe MAlonzo.Code.Algebra.Structures.d2488
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     v3
                     v4
                     v5
                     v6)
                  v8)
               (coe MAlonzo.Code.Function.du176 v7
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     v3
                     v4
                     v5
                     v6)
                  v8))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v4 v6)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v4 v6)))
               (coe v1 v4 v6)
               (coe v1 v4 v6)
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe v1 v4 v6)
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v4 v6)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4 v6))))
                  (coe v2 v4 v6))
               (coe du144 v0 (coe v1 v4 v6)))))
name422
  = "Algebra.Properties.BooleanAlgebra.XorRing.\8853-identity"
d422 v0 v1 v2 v3 v4 = du422 v2 v3 v4
du422 v0 v1 v2
  = coe MAlonzo.Code.Data.Product.C30
      (coe d430 erased erased v0 v1 v2)
      (\ v3 ->
         coe MAlonzo.Code.Function.du176
           (coe du382 v0 v1 v2 v3 (coe MAlonzo.Code.Algebra.d1420 v0))
           (coe MAlonzo.Code.Relation.Binary.Core.d520
              (coe MAlonzo.Code.Algebra.Structures.d2482
                 (coe MAlonzo.Code.Algebra.Structures.d2630
                    (coe MAlonzo.Code.Algebra.Structures.d2798
                       (coe MAlonzo.Code.Algebra.d1422 v0))))
              (coe v1 v3 (coe MAlonzo.Code.Algebra.d1420 v0))
              (coe v1 (coe MAlonzo.Code.Algebra.d1420 v0) v3)
              v3)
           (coe du430 v0 v1 v2 v3))
name430
  = "Algebra.Properties.BooleanAlgebra.XorRing._.\8869\8853x=x"
d430 v0 v1 v2 v3 v4 v5 = du430 v2 v3 v4 v5
du430 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe v1 (coe MAlonzo.Code.Algebra.d1420 v0) v3)
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1420 v0)
               v3)
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1420 v0)
                  v3)))
         v3
         (coe v2 (coe MAlonzo.Code.Algebra.d1420 v0) v3)
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1420 v0)
                  v3)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1420 v0)
                     v3)))
            (coe MAlonzo.Code.Algebra.d1414 v0 v3
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1420 v0)))
            v3
            (coe du352 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1420 v0)
                  v3)
               v3
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1420 v0)
                  v3)
               (coe MAlonzo.Code.Algebra.d1420 v0)
               (coe MAlonzo.Code.Data.Product.d26 (coe du198 v0) v3)
               (coe MAlonzo.Code.Data.Product.d26 (coe du212 v0) v3))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v3
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1420 v0)))
               (coe MAlonzo.Code.Algebra.d1414 v0 v3
                  (coe MAlonzo.Code.Algebra.d1418 v0))
               v3
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Relation.Binary.Core.d516
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     v3)
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     v3
                     v3
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1420 v0))
                     (coe MAlonzo.Code.Algebra.d1418 v0))
                  (coe du262 v0))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3
                     (coe MAlonzo.Code.Algebra.d1418 v0))
                  v3
                  v3
                  (coe MAlonzo.Code.Data.Product.d28 (coe du184 v0) v3)
                  (coe du144 v0 v3)))))
name436 = "Algebra.Properties.BooleanAlgebra.XorRing.\8853-inverse"
d436 v0 v1 v2 v3 v4 = du436 v2 v3 v4
du436 v0 v1 v2
  = coe MAlonzo.Code.Data.Product.C30
      (coe d444 erased erased v0 v1 v2)
      (\ v3 ->
         coe MAlonzo.Code.Function.du176 (coe du382 v0 v1 v2 v3 v3)
           (coe MAlonzo.Code.Relation.Binary.Core.d520
              (coe MAlonzo.Code.Algebra.Structures.d2482
                 (coe MAlonzo.Code.Algebra.Structures.d2630
                    (coe MAlonzo.Code.Algebra.Structures.d2798
                       (coe MAlonzo.Code.Algebra.d1422 v0))))
              (coe v1 v3 v3)
              (coe v1 v3 v3)
              (coe MAlonzo.Code.Algebra.d1420 v0))
           (coe du444 v0 v1 v2 v3))
name444
  = "Algebra.Properties.BooleanAlgebra.XorRing._.x\8853x=\8869"
d444 v0 v1 v2 v3 v4 v5 = du444 v2 v3 v4 v5
du444 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe v1 v3 v3)
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v3 v3)
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v3 v3)))
         (coe MAlonzo.Code.Algebra.d1420 v0)
         (coe v2 v3 v3)
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v3 v3)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3 v3)))
            (coe MAlonzo.Code.Algebra.d1414 v0 v3
               (coe MAlonzo.Code.Algebra.d1416 v0 v3))
            (coe MAlonzo.Code.Algebra.d1420 v0)
            (coe du352 v0 (coe MAlonzo.Code.Algebra.d1412 v0 v3 v3) v3
               (coe MAlonzo.Code.Algebra.d1414 v0 v3 v3)
               v3
               (coe du90 v0 v3)
               (coe du78 v0 v3))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v3
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))
               (coe MAlonzo.Code.Algebra.d1420 v0)
               (coe MAlonzo.Code.Algebra.d1420 v0)
               (coe MAlonzo.Code.Data.Product.d28 (coe du170 v0) v3)
               (coe du144 v0 (coe MAlonzo.Code.Algebra.d1420 v0)))))
name450
  = "Algebra.Properties.BooleanAlgebra.XorRing.distrib-\8743-\8853"
d450 v0 v1 v2 v3 v4 = du450 v2 v3 v4
du450 v0 v1 v2
  = coe MAlonzo.Code.Data.Product.C30
      (coe d456 erased erased v0 v1 v2)
      (coe d474 erased erased v0 v1 v2)
name456 = "Algebra.Properties.BooleanAlgebra.XorRing._.dist\737"
d456 v0 v1 v2 v3 v4 v5 v6 v7 = du456 v2 v3 v4 v5 v6 v7
du456 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe MAlonzo.Code.Algebra.d1414 v0 v3 (coe v1 v4 v5))
         (coe MAlonzo.Code.Algebra.d1414 v0 v3
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
         (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
            (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               v3)
            (coe MAlonzo.Code.Algebra.Structures.d2494
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               v3
               v3
               (coe v1 v4 v5)
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
            (coe v2 v4 v5))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v3
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v3
                  (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5)))
            (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
            (coe MAlonzo.Code.Function.du158
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3
                        (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5)))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5)))))
               (coe MAlonzo.Code.Algebra.Structures.d2492
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  v3
                  (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3
                     (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3
                     (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v5)))
               (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Relation.Binary.Core.d516
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3
                        (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)))
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3
                        (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3
                        (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v5)))
                  (coe du274 v0 v4 v5))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3
                        (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v5)))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1420 v0)
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3
                           (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                  (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                  (coe MAlonzo.Code.Function.du158
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1420 v0)
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                     (coe MAlonzo.Code.Data.Product.d26 (coe du198 v0)
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v5)))))
                  (coe du146 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1420 v0)
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                     (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                     (coe MAlonzo.Code.Function.du176 (coe du472 v0 v3 v4 v5)
                        (coe MAlonzo.Code.Algebra.Structures.d2488
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1420 v0)
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v5)))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe MAlonzo.Code.Algebra.Structures.d2482
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0))))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v5)))))
                     (coe du146 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                        (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                        (coe MAlonzo.Code.Function.du158
                           (coe MAlonzo.Code.Relation.Binary.Core.d518
                              (coe MAlonzo.Code.Algebra.Structures.d2482
                                 (coe MAlonzo.Code.Algebra.Structures.d2630
                                    (coe MAlonzo.Code.Algebra.Structures.d2798
                                       (coe MAlonzo.Code.Algebra.d1422 v0))))
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5)))))
                           (coe MAlonzo.Code.Data.Product.d26 (coe du80 v0)
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                        (coe du146 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 (coe MAlonzo.Code.Algebra.d1416 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
                           (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                              (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                           (coe MAlonzo.Code.Function.du176
                              (coe MAlonzo.Code.Relation.Binary.Core.d516
                                 (coe MAlonzo.Code.Algebra.Structures.d2482
                                    (coe MAlonzo.Code.Algebra.Structures.d2630
                                       (coe MAlonzo.Code.Algebra.Structures.d2798
                                          (coe MAlonzo.Code.Algebra.d1422 v0))))
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)))
                              (coe MAlonzo.Code.Algebra.Structures.d2494
                                 (coe MAlonzo.Code.Algebra.Structures.d2630
                                    (coe MAlonzo.Code.Algebra.Structures.d2798
                                       (coe MAlonzo.Code.Algebra.d1422 v0)))
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5)))
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
                              (coe MAlonzo.Code.Function.du176
                                 (coe MAlonzo.Code.Relation.Binary.Core.d516
                                    (coe MAlonzo.Code.Algebra.Structures.d2482
                                       (coe MAlonzo.Code.Algebra.Structures.d2630
                                          (coe MAlonzo.Code.Algebra.Structures.d2798
                                             (coe MAlonzo.Code.Algebra.d1422 v0))))
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                                 (coe MAlonzo.Code.Algebra.Structures.d2488
                                    (coe MAlonzo.Code.Algebra.Structures.d2630
                                       (coe MAlonzo.Code.Algebra.Structures.d2798
                                          (coe MAlonzo.Code.Algebra.d1422 v0)))
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5)))
                                 (coe MAlonzo.Code.Relation.Binary.Core.d518
                                    (coe MAlonzo.Code.Algebra.Structures.d2482
                                       (coe MAlonzo.Code.Algebra.Structures.d2630
                                          (coe MAlonzo.Code.Algebra.Structures.d2798
                                             (coe MAlonzo.Code.Algebra.d1422 v0))))
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                    (coe du274 v0 v4 v5))))
                           (coe du146 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                 (coe MAlonzo.Code.Algebra.d1416 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
                              (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                              (coe MAlonzo.Code.Function.du176
                                 (coe MAlonzo.Code.Relation.Binary.Core.d516
                                    (coe MAlonzo.Code.Algebra.Structures.d2482
                                       (coe MAlonzo.Code.Algebra.Structures.d2630
                                          (coe MAlonzo.Code.Algebra.Structures.d2798
                                             (coe MAlonzo.Code.Algebra.d1422 v0))))
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)))
                                 (coe MAlonzo.Code.Algebra.Structures.d2494
                                    (coe MAlonzo.Code.Algebra.Structures.d2630
                                       (coe MAlonzo.Code.Algebra.Structures.d2798
                                          (coe MAlonzo.Code.Algebra.d1422 v0)))
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       (coe MAlonzo.Code.Algebra.d1416 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5)))
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
                                 (coe MAlonzo.Code.Relation.Binary.Core.d518
                                    (coe MAlonzo.Code.Algebra.Structures.d2482
                                       (coe MAlonzo.Code.Algebra.Structures.d2630
                                          (coe MAlonzo.Code.Algebra.Structures.d2798
                                             (coe MAlonzo.Code.Algebra.d1422 v0))))
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5)))
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       (coe MAlonzo.Code.Algebra.d1416 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5)))
                                    (coe du274 v0 v3 (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
                              (coe du146 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))))
                                 (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                                 (coe du352 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                                    (coe MAlonzo.Code.Relation.Binary.Core.d516
                                       (coe MAlonzo.Code.Algebra.Structures.d2482
                                          (coe MAlonzo.Code.Algebra.Structures.d2630
                                             (coe MAlonzo.Code.Algebra.Structures.d2798
                                                (coe MAlonzo.Code.Algebra.d1422 v0))))
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)))
                                    (coe du470 v0 v3 v4 v5))
                                 (coe du146 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                       (coe MAlonzo.Code.Algebra.d1416 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))))
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                                       (coe MAlonzo.Code.Algebra.d1416 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))))
                                    (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                       (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                                    (coe MAlonzo.Code.Function.du176
                                       (coe MAlonzo.Code.Data.Product.d26 (coe du80 v0) v3 v4 v5)
                                       (coe MAlonzo.Code.Algebra.Structures.d2494
                                          (coe MAlonzo.Code.Algebra.Structures.d2630
                                             (coe MAlonzo.Code.Algebra.Structures.d2798
                                                (coe MAlonzo.Code.Algebra.d1422 v0)))
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v3
                                             (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5))
                                          (coe MAlonzo.Code.Algebra.d1412 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                                          (coe MAlonzo.Code.Algebra.d1416 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5)))
                                          (coe MAlonzo.Code.Algebra.d1416 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))))
                                       (coe MAlonzo.Code.Relation.Binary.Core.d516
                                          (coe MAlonzo.Code.Algebra.Structures.d2482
                                             (coe MAlonzo.Code.Algebra.Structures.d2630
                                                (coe MAlonzo.Code.Algebra.Structures.d2798
                                                   (coe MAlonzo.Code.Algebra.d1422 v0))))
                                          (coe MAlonzo.Code.Algebra.d1416 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5)))))
                                    (coe du146 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                                          (coe MAlonzo.Code.Algebra.d1416 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))))
                                       (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                                       (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                                       (coe MAlonzo.Code.Function.du158
                                          (coe MAlonzo.Code.Relation.Binary.Core.d518
                                             (coe MAlonzo.Code.Algebra.Structures.d2482
                                                (coe MAlonzo.Code.Algebra.Structures.d2630
                                                   (coe MAlonzo.Code.Algebra.Structures.d2798
                                                      (coe MAlonzo.Code.Algebra.d1422 v0))))
                                             (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                                             (coe MAlonzo.Code.Algebra.d1414 v0
                                                (coe MAlonzo.Code.Algebra.d1412 v0
                                                   (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                                   (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
                                                (coe MAlonzo.Code.Algebra.d1416 v0
                                                   (coe MAlonzo.Code.Algebra.d1414 v0
                                                      (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                                      (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5)))))
                                          (coe v2 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5)))
                                       (coe du144 v0
                                          (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))))))))))))))
name468 = "Algebra.Properties.BooleanAlgebra.XorRing._._.lem\8322"
d468 v0 v1 v2 v3 v4 v5 v6 v7 = du468 v2 v5 v6 v7
du468 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0 v1
            (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
            v3)
         (coe MAlonzo.Code.Algebra.d1414 v0 v2
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                  v3)
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3)))
            (coe MAlonzo.Code.Algebra.Structures.d2492
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               v1
               v2
               v3))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
               v3)
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v2 v1)
               v3)
            (coe MAlonzo.Code.Algebra.d1414 v0 v2
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Algebra.Structures.d2490
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  v1
                  v2)
               (coe MAlonzo.Code.Algebra.Structures.d2494
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1414 v0 v2 v1)
                  v3
                  v3)
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  v3))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v2 v1)
                  v3)
               (coe MAlonzo.Code.Algebra.d1414 v0 v2
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))
               (coe MAlonzo.Code.Algebra.d1414 v0 v2
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))
               (coe MAlonzo.Code.Algebra.Structures.d2492
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  v2
                  v1
                  v3)
               (coe du144 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v2
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))))))
name470 = "Algebra.Properties.BooleanAlgebra.XorRing._._.lem\8321"
d470 v0 v1 v2 v3 v4 v5 v6 v7 = du470 v2 v5 v6 v7
du470 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0 v1
            (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v1)
            (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v1)
               v1
               (coe du78 v0 v1))
            (coe MAlonzo.Code.Algebra.Structures.d2494
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               v1
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v1)
               (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3)
               (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v1)
               (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.d1414 v0 v1
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))
            (coe MAlonzo.Code.Algebra.Structures.d2492
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               v1
               v1
               (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3)))
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1414 v0 v2
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Relation.Binary.Core.d516
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     v1)
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     v1
                     v1
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3)))
                  (coe du468 v0 v1 v2 v3))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))
                  (coe MAlonzo.Code.Function.du158
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1
                           (coe MAlonzo.Code.Algebra.d1414 v0 v2
                              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3))))
                     (coe MAlonzo.Code.Algebra.Structures.d2492
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        v1
                        v2
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3)))
                  (coe du144 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v3)))))))
name472 = "Algebra.Properties.BooleanAlgebra.XorRing._._.lem\8323"
d472 v0 v1 v2 v3 v4 v5 v6 v7 = du472 v2 v5 v6 v7
du472 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe MAlonzo.Code.Algebra.d1420 v0)
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
            (coe MAlonzo.Code.Algebra.d1420 v0))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1
               (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.d1416 v0 v1))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1420 v0))
               (coe MAlonzo.Code.Algebra.d1420 v0))
            (coe MAlonzo.Code.Data.Product.d28 (coe du212 v0)
               (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
               (coe MAlonzo.Code.Algebra.d1420 v0))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
               (coe MAlonzo.Code.Algebra.d1416 v0 v1))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
               (coe MAlonzo.Code.Algebra.Structures.d2494
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1420 v0)
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1420 v0)
                  (coe MAlonzo.Code.Data.Product.d28 (coe du170 v0) v1)))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                     v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                           v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1))))
                  (coe MAlonzo.Code.Algebra.Structures.d2492
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                     v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                        v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1
                        (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Algebra.Structures.d2490
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                        v1)
                     (coe MAlonzo.Code.Algebra.Structures.d2494
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                           v1)
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1
                           (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1))
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)))
                  (coe du144 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1
                           (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)))))))
name474 = "Algebra.Properties.BooleanAlgebra.XorRing._.dist\691"
d474 v0 v1 v2 v3 v4 v5 v6 v7 = du474 v2 v3 v4 v5 v6 v7
du474 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0 (coe MAlonzo.Code.Algebra.d1414 v0 (coe v1 v4 v5) v3)
         (coe MAlonzo.Code.Algebra.d1414 v0 v3 (coe v1 v4 v5))
         (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)
            (coe MAlonzo.Code.Algebra.d1414 v0 v5 v3))
         (coe MAlonzo.Code.Algebra.Structures.d2490
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))
            (coe v1 v4 v5)
            v3)
         (coe du146 v0 (coe MAlonzo.Code.Algebra.d1414 v0 v3 (coe v1 v4 v5))
            (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
            (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)
               (coe MAlonzo.Code.Algebra.d1414 v0 v5 v3))
            (coe du456 v0 v1 v2 v3 v4 v5)
            (coe du146 v0
               (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                  (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5))
               (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)
                  (coe MAlonzo.Code.Algebra.d1414 v0 v5 v3))
               (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)
                  (coe MAlonzo.Code.Algebra.d1414 v0 v5 v3))
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Algebra.Structures.d2490
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     v3
                     v4)
                  (coe d408 erased erased v0 v1 v2
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3 v5)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v5 v3))
                  (coe MAlonzo.Code.Algebra.Structures.d2490
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     v3
                     v5))
               (coe du144 v0
                  (coe v1 (coe MAlonzo.Code.Algebra.d1414 v0 v4 v3)
                     (coe MAlonzo.Code.Algebra.d1414 v0 v5 v3))))))
name490 = "Algebra.Properties.BooleanAlgebra.XorRing.lemma\8322"
d490 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du490 v2 v5 v6 v7 v8
du490 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
               v3)
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
               v4))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v3)
               (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v4)
               (coe MAlonzo.Code.Algebra.d1412 v0 v2 v4)))
         (coe MAlonzo.Code.Data.Product.d26 (coe du92 v0)
            (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
            v3
            v4)
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                  v3)
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                  v4))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v4)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v4)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v4)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v4)))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Data.Product.d28 (coe du92 v0) v3 v1 v2)
               (coe MAlonzo.Code.Algebra.Structures.d2494
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     v3)
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v3)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)
                     v4)
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v4)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2 v4)))
               (coe MAlonzo.Code.Data.Product.d28 (coe du92 v0) v4 v1 v2))
            (coe du144 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v3)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v4)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2 v4))))))
name500 = "Algebra.Properties.BooleanAlgebra.XorRing.\8853-assoc"
d500 v0 v1 v2 v3 v4 v5 v6 v7 = du500 v2 v3 v4 v5 v6 v7
du500 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Function.du158
      (coe MAlonzo.Code.Relation.Binary.Core.d518
         (coe MAlonzo.Code.Algebra.Structures.d2482
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0))))
         (coe v1 v3 (coe v1 v4 v5))
         (coe v1 (coe v1 v3 v4) v5))
      (coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
         (coe du146 v0 (coe v1 v3 (coe v1 v4 v5))
            (coe v1 v3
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
            (coe v1 (coe v1 v3 v4) v5)
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  v3)
               (coe d408 erased erased v0 v1 v2 v3 v3 (coe v1 v4 v5)
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
               (coe v2 v4 v5))
            (coe du146 v0
               (coe v1 v3
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v3
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v3
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))))
               (coe v1 (coe v1 v3 v4) v5)
               (coe v2 v3
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v3
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v3
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                           v5)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v3
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                           (coe MAlonzo.Code.Algebra.d1416 v0 v5)))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                           v5)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                              v4)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                  (coe v1 (coe v1 v3 v4) v5)
                  (coe MAlonzo.Code.Function.du176 (coe du518 v0 v3 v4 v5)
                     (coe MAlonzo.Code.Algebra.Structures.d2494
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1412 v0 v3
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5))))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                              v5)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                              (coe MAlonzo.Code.Algebra.d1416 v0 v5)))
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v3
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v4 v5)
                                 (coe MAlonzo.Code.Algebra.d1416 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0 v4 v5)))))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                              v5)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 v4)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                     (coe du522 v0 v3 v4 v5))
                  (coe du146 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                              v5)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                              (coe MAlonzo.Code.Algebra.d1416 v0 v5)))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                              v5)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 v4)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                           v5)
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                              (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                 v5)
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    v4)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v5)))))
                     (coe v1 (coe v1 v3 v4) v5)
                     (coe MAlonzo.Code.Algebra.Structures.d2492
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                           v5)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v3
                              (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                           (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                              v5)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                 v4)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                     (coe du146 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                              v5)
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                    v5)
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       v4)
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v5)))))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                              v5)
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                 v5)
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       v4)
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v5)))))
                        (coe v1 (coe v1 v3 v4) v5)
                        (coe MAlonzo.Code.Function.du176
                           (coe MAlonzo.Code.Relation.Binary.Core.d516
                              (coe MAlonzo.Code.Algebra.Structures.d2482
                                 (coe MAlonzo.Code.Algebra.Structures.d2630
                                    (coe MAlonzo.Code.Algebra.Structures.d2798
                                       (coe MAlonzo.Code.Algebra.d1422 v0))))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                 v5))
                           (coe MAlonzo.Code.Algebra.Structures.d2494
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0)))
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                 v5)
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                 v5)
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                       v5)
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                          v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                    v5)
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                          v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5)))))
                           (coe du524 v0 v3 v4 v5))
                        (coe du146 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                 v5)
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                    v5)
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                          v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5)))))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                    v5)
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                    v5))
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       v4)
                                    (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                           (coe v1 (coe v1 v3 v4) v5)
                           (coe MAlonzo.Code.Function.du158
                              (coe MAlonzo.Code.Relation.Binary.Core.d518
                                 (coe MAlonzo.Code.Algebra.Structures.d2482
                                    (coe MAlonzo.Code.Algebra.Structures.d2630
                                       (coe MAlonzo.Code.Algebra.Structures.d2798
                                          (coe MAlonzo.Code.Algebra.d1422 v0))))
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                          v5)
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                          v5))
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                             v4)
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                       v5)
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                          v5)
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0
                                             (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                                (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                          (coe MAlonzo.Code.Algebra.d1412 v0
                                             (coe MAlonzo.Code.Algebra.d1412 v0
                                                (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                                v4)
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v5))))))
                              (coe MAlonzo.Code.Algebra.Structures.d2492
                                 (coe MAlonzo.Code.Algebra.Structures.d2630
                                    (coe MAlonzo.Code.Algebra.Structures.d2798
                                       (coe MAlonzo.Code.Algebra.d1422 v0)))
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                    v5)
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                    v5)
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                          v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5)))))
                           (coe du146 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                       v5)
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                       v5))
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                          v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0 v5))))
                              (coe MAlonzo.Code.Algebra.d1414 v0
                                 (coe MAlonzo.Code.Algebra.d1412 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                    v5)
                                 (coe MAlonzo.Code.Algebra.d1416 v0
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                          (coe MAlonzo.Code.Algebra.d1416 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                       v5)))
                              (coe v1 (coe v1 v3 v4) v5)
                              (coe MAlonzo.Code.Function.du176 (coe du512 v0 v3 v4 v5)
                                 (coe MAlonzo.Code.Algebra.Structures.d2494
                                    (coe MAlonzo.Code.Algebra.Structures.d2630
                                       (coe MAlonzo.Code.Algebra.Structures.d2798
                                          (coe MAlonzo.Code.Algebra.d1422 v0)))
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                          v5)
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                          v5))
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                          (coe MAlonzo.Code.Algebra.d1416 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                       v5)
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v3
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v4))
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v5))
                                       (coe MAlonzo.Code.Algebra.d1412 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0
                                             (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                                             v4)
                                          (coe MAlonzo.Code.Algebra.d1416 v0 v5)))
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0
                                             (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                             (coe MAlonzo.Code.Algebra.d1416 v0
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                          v5)))
                                 (coe du516 v0 v3 v4 v5))
                              (coe du146 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0
                                    (coe MAlonzo.Code.Algebra.d1412 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                          (coe MAlonzo.Code.Algebra.d1416 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                       v5)
                                    (coe MAlonzo.Code.Algebra.d1416 v0
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0
                                             (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                             (coe MAlonzo.Code.Algebra.d1416 v0
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                          v5)))
                                 (coe v1
                                    (coe MAlonzo.Code.Algebra.d1414 v0
                                       (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                       (coe MAlonzo.Code.Algebra.d1416 v0
                                          (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                    v5)
                                 (coe v1 (coe v1 v3 v4) v5)
                                 (coe MAlonzo.Code.Function.du158
                                    (coe MAlonzo.Code.Relation.Binary.Core.d518
                                       (coe MAlonzo.Code.Algebra.Structures.d2482
                                          (coe MAlonzo.Code.Algebra.Structures.d2630
                                             (coe MAlonzo.Code.Algebra.Structures.d2798
                                                (coe MAlonzo.Code.Algebra.d1422 v0))))
                                       (coe v1
                                          (coe MAlonzo.Code.Algebra.d1414 v0
                                             (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                             (coe MAlonzo.Code.Algebra.d1416 v0
                                                (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                          v5)
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0
                                                (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                                (coe MAlonzo.Code.Algebra.d1416 v0
                                                   (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                             v5)
                                          (coe MAlonzo.Code.Algebra.d1416 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0
                                                (coe MAlonzo.Code.Algebra.d1414 v0
                                                   (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                                   (coe MAlonzo.Code.Algebra.d1416 v0
                                                      (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                                v5))))
                                    (coe v2
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                          (coe MAlonzo.Code.Algebra.d1416 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                       v5))
                                 (coe du146 v0
                                    (coe v1
                                       (coe MAlonzo.Code.Algebra.d1414 v0
                                          (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                          (coe MAlonzo.Code.Algebra.d1416 v0
                                             (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                       v5)
                                    (coe v1 (coe v1 v3 v4) v5)
                                    (coe v1 (coe v1 v3 v4) v5)
                                    (coe MAlonzo.Code.Function.du158
                                       (coe MAlonzo.Code.Relation.Binary.Core.d518
                                          (coe MAlonzo.Code.Algebra.Structures.d2482
                                             (coe MAlonzo.Code.Algebra.Structures.d2630
                                                (coe MAlonzo.Code.Algebra.Structures.d2798
                                                   (coe MAlonzo.Code.Algebra.d1422 v0))))
                                          (coe v1 (coe v1 v3 v4) v5)
                                          (coe v1
                                             (coe MAlonzo.Code.Algebra.d1414 v0
                                                (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                                (coe MAlonzo.Code.Algebra.d1416 v0
                                                   (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                             v5))
                                       (coe MAlonzo.Code.Function.du176 (coe v2 v3 v4)
                                          (coe d408 erased erased v0 v1 v2 (coe v1 v3 v4)
                                             (coe MAlonzo.Code.Algebra.d1414 v0
                                                (coe MAlonzo.Code.Algebra.d1412 v0 v3 v4)
                                                (coe MAlonzo.Code.Algebra.d1416 v0
                                                   (coe MAlonzo.Code.Algebra.d1414 v0 v3 v4)))
                                             v5
                                             v5)
                                          (coe MAlonzo.Code.Relation.Binary.Core.d516
                                             (coe MAlonzo.Code.Algebra.Structures.d2482
                                                (coe MAlonzo.Code.Algebra.Structures.d2630
                                                   (coe MAlonzo.Code.Algebra.Structures.d2798
                                                      (coe MAlonzo.Code.Algebra.d1422 v0))))
                                             v5)))
                                    (coe du144 v0 (coe v1 (coe v1 v3 v4) v5))))))))))))
name512 = "Algebra.Properties.BooleanAlgebra.XorRing._.lem\8321"
d512 v0 v1 v2 v3 v4 v5 v6 v7 = du512 v2 v5 v6 v7
du512 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
               v3)
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               v3))
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
            v3)
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
            v3)
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                  v3)
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     v3)))
            (coe MAlonzo.Code.Data.Product.d28 (coe du92 v0) v3
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               v3)
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
               v3)
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
               v3)
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Relation.Binary.Core.d516
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe du274 v0 v1 v2)))
               (coe MAlonzo.Code.Algebra.Structures.d2488
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                  v3
                  v3)
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  v3))
            (coe du144 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                  v3))))
name514 = "Algebra.Properties.BooleanAlgebra.XorRing._.lem\8322'"
d514 v0 v1 v2 v3 v4 v5 v6 v7 = du514 v2 v5 v6
du514 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v2))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               v2))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1418 v0)
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v2)
               (coe MAlonzo.Code.Algebra.d1418 v0)))
         (coe MAlonzo.Code.Algebra.d1416 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1418 v0)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1418 v0)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Data.Product.d26 (coe du184 v0)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               (coe MAlonzo.Code.Algebra.Structures.d2494
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1418 v0)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1418 v0))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2))
               (coe MAlonzo.Code.Data.Product.d28 (coe du184 v0)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2))))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1418 v0)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1418 v0)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v1)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                     v1))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                     v2)))
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
            (coe MAlonzo.Code.Function.du158
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v1)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v1))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v2)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1418 v0)
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1418 v0))))
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Data.Product.d26 (coe du160 v0) v1)
                     (coe MAlonzo.Code.Algebra.Structures.d2494
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v1)
                        (coe MAlonzo.Code.Algebra.d1418 v0)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v1)
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                     (coe MAlonzo.Code.Algebra.Structures.d2484
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                        v1))
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v1)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v1))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1418 v0)
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v2))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1418 v0)))
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2))
                     (coe MAlonzo.Code.Algebra.Structures.d2494
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1418 v0))
                     (coe MAlonzo.Code.Data.Product.d26 (coe du160 v0) v2))))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v1)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                        v1))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                        v2)))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v1)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                              v1))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                              v2))))
                  (coe du490 v0 (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                     v1
                     v2))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                  (coe MAlonzo.Code.Function.du158
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                     (coe MAlonzo.Code.Function.du176 (coe du294 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Structures.d2488
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))
                        (coe du266 v0 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                  (coe du146 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                        (coe du274 v0 (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                     (coe du144 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))))))))
name516 = "Algebra.Properties.BooleanAlgebra.XorRing._.lem\8322"
d516 v0 v1 v2 v3 v4 v5 v6 v7 = du516 v2 v5 v6 v7
du516 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Algebra.d1416 v0 v3))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v2)
               (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v2))
            (coe MAlonzo.Code.Algebra.d1416 v0 v3))
         (coe MAlonzo.Code.Algebra.d1416 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
               v3))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
            (coe MAlonzo.Code.Data.Product.d28 (coe du92 v0)
               (coe MAlonzo.Code.Algebra.d1416 v0 v3)
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v2)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2))
               (coe MAlonzo.Code.Algebra.d1416 v0 v3))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
               (coe MAlonzo.Code.Algebra.d1416 v0 v3))
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                  v3))
            (coe MAlonzo.Code.Function.du176 (coe du514 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Structures.d2488
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                     v3))
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                     v3))
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                           v3))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                              (coe MAlonzo.Code.Algebra.d1416 v0
                                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                  (coe du274 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                     v3))
               (coe du144 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0
                              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                        v3))))))
name518 = "Algebra.Properties.BooleanAlgebra.XorRing._.lem\8323"
d518 v0 v1 v2 v3 v4 v5 v6 v7 = du518 v2 v5 v6 v7
du518 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1412 v0 v1
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))))
         (coe MAlonzo.Code.Algebra.d1412 v0 v1
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
               v3)
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               v1)
            (coe MAlonzo.Code.Algebra.Structures.d2488
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               v1
               v1
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
               (coe MAlonzo.Code.Algebra.Structures.d2494
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
               (coe du274 v0 v2 v3)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v1
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                  v3)
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
            (coe MAlonzo.Code.Data.Product.d26 (coe du92 v0) v1
               (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                     v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                        v3)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
                     (coe MAlonzo.Code.Algebra.Structures.d2486
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        v1
                        v2
                        v3))
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                        v3)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                     (coe MAlonzo.Code.Algebra.Structures.d2486
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
               (coe du144 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
                        v3)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3)))))))
name520 = "Algebra.Properties.BooleanAlgebra.XorRing._.lem\8324'"
d520 v0 v1 v2 v3 v4 v5 v6 v7 = du520 v2 v6 v7
du520 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1416 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0 v1
               (coe MAlonzo.Code.Algebra.d1416 v0 v2))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               v2))
         (coe du274 v0 (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v2))
            (coe MAlonzo.Code.Function.du176 (coe du294 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Structures.d2488
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))
               (coe du266 v0 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v1)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                        v1))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                        v2)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2))
               (coe du490 v0 (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                  v1
                  v2)
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v1)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v1))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v2)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1418 v0)
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1418 v0)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2))
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Data.Product.d26 (coe du160 v0) v1)
                        (coe MAlonzo.Code.Algebra.Structures.d2494
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v1)
                           (coe MAlonzo.Code.Algebra.d1418 v0)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                              v1)
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                        (coe MAlonzo.Code.Algebra.Structures.d2484
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v1))
                     (coe MAlonzo.Code.Algebra.Structures.d2494
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v1)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                              v1))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1418 v0)
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                              v2))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1418 v0)))
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe MAlonzo.Code.Algebra.Structures.d2482
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0))))
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2))
                        (coe MAlonzo.Code.Algebra.Structures.d2494
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1418 v0))
                        (coe MAlonzo.Code.Data.Product.d26 (coe du160 v0) v2)))
                  (coe du146 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1418 v0)
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1418 v0)))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2))
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Data.Product.d26 (coe du184 v0)
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                        (coe MAlonzo.Code.Algebra.Structures.d2494
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1418 v0)
                              (coe MAlonzo.Code.Algebra.d1412 v0 v1
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v2)))
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           (coe MAlonzo.Code.Algebra.d1414 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                                 v2)
                              (coe MAlonzo.Code.Algebra.d1418 v0))
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2))
                        (coe MAlonzo.Code.Data.Product.d28 (coe du184 v0)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)))
                     (coe du144 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2))))))))
name522 = "Algebra.Properties.BooleanAlgebra.XorRing._.lem\8324"
d522 v0 v1 v2 v3 v4 v5 v6 v7 = du522 v2 v5 v6 v7
du522 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1416 v0
            (coe MAlonzo.Code.Algebra.d1414 v0 v1
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3)))))
         (coe MAlonzo.Code.Algebra.d1412 v0
            (coe MAlonzo.Code.Algebra.d1416 v0 v1)
            (coe MAlonzo.Code.Algebra.d1416 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3)))))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               v3)
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v2)
               (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
         (coe du274 v0 v1
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               (coe MAlonzo.Code.Algebra.d1416 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                     (coe MAlonzo.Code.Algebra.d1416 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3)))))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1416 v0 v1)
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                     v3)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  v3)
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1))
               (coe MAlonzo.Code.Algebra.Structures.d2488
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v2 v3)
                        (coe MAlonzo.Code.Algebra.d1416 v0
                           (coe MAlonzo.Code.Algebra.d1414 v0 v2 v3))))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                        v3)))
               (coe du520 v0 v2 v3))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                        v3)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1412 v0 v2
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                        v3)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
               (coe MAlonzo.Code.Data.Product.d26 (coe du92 v0)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1412 v0 v2
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                     v3))
               (coe du146 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1412 v0 v2
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v3)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        v3))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        v3)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1412 v0 v2
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                        (coe MAlonzo.Code.Algebra.Structures.d2486
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                     (coe MAlonzo.Code.Algebra.Structures.d2494
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1412 v0 v2
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                              v3))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           v3))
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0))))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           v3)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                              v3))
                        (coe MAlonzo.Code.Algebra.Structures.d2486
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.Structures.d2798
                                 (coe MAlonzo.Code.Algebra.d1422 v0)))
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2)
                           v3)))
                  (coe du146 v0
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           v3))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           v3)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           v3)
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                     (coe MAlonzo.Code.Algebra.Structures.d2490
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0)))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           v3))
                     (coe du144 v0
                        (coe MAlonzo.Code.Algebra.d1414 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                              v3)
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1412 v0
                                 (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                                 v2)
                              (coe MAlonzo.Code.Algebra.d1416 v0 v3)))))))))
name524 = "Algebra.Properties.BooleanAlgebra.XorRing._.lem\8325"
d524 v0 v1 v2 v3 v4 v5 v6 v7 = du524 v2 v5 v6 v7
du524 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du146 v0
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0 v1
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               (coe MAlonzo.Code.Algebra.d1416 v0 v3))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  v3)
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  v3))
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  v2)
               (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
         (coe MAlonzo.Code.Algebra.d1414 v0
            (coe MAlonzo.Code.Algebra.d1412 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v2))
               v3)
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        v3)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3)))))
            (coe MAlonzo.Code.Algebra.Structures.d2492
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.Structures.d2798
                     (coe MAlonzo.Code.Algebra.d1422 v0)))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0 v1
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  v3)
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
         (coe du146 v0
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     v3))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
            (coe MAlonzo.Code.Algebra.d1414 v0
               (coe MAlonzo.Code.Algebra.d1412 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                  v3)
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Algebra.Structures.d2490
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     v3))
               (coe MAlonzo.Code.Algebra.Structures.d2494
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        v3))
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        v3)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0))))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
            (coe du146 v0
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        v3)
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     v3)
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
               (coe MAlonzo.Code.Algebra.d1414 v0
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     v3)
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0 v1
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v3))))
               (coe MAlonzo.Code.Algebra.Structures.d2492
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     v3)
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0 v1
                        (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                  (coe MAlonzo.Code.Algebra.d1412 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1416 v0 v3)))
               (coe du144 v0
                  (coe MAlonzo.Code.Algebra.d1414 v0
                     (coe MAlonzo.Code.Algebra.d1412 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                        v3)
                     (coe MAlonzo.Code.Algebra.d1414 v0
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0 v1
                              (coe MAlonzo.Code.Algebra.d1416 v0 v2))
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3))
                        (coe MAlonzo.Code.Algebra.d1412 v0
                           (coe MAlonzo.Code.Algebra.d1412 v0
                              (coe MAlonzo.Code.Algebra.d1416 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1416 v0 v3))))))))
name526
  = "Algebra.Properties.BooleanAlgebra.XorRing.isCommutativeRing"
d526 v0 v1 v2 v3 v4 = du526 v2 v3 v4
du526 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.C475
      (coe MAlonzo.Code.Algebra.Structures.C363
         (coe MAlonzo.Code.Algebra.Structures.C137
            (coe MAlonzo.Code.Algebra.Structures.C109
               (coe MAlonzo.Code.Algebra.Structures.C49
                  (coe MAlonzo.Code.Algebra.Structures.C25
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))))
                     (coe d500 erased erased v0 v1 v2)
                     (coe d408 erased erased v0 v1 v2))
                  (coe du422 v0 v1 v2))
               (coe du436 v0 v1 v2)
               (\ v3 v4 -> coe MAlonzo.Code.Function.d68 erased erased))
            (coe d382 erased erased v0 v1 v2))
         (coe MAlonzo.Code.Algebra.Structures.C49
            (coe MAlonzo.Code.Algebra.Structures.C25
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.Structures.d2492
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0))))
               (coe MAlonzo.Code.Algebra.Structures.d2494
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.Structures.d2798
                        (coe MAlonzo.Code.Algebra.d1422 v0)))))
            (coe du184 v0))
         (coe du450 v0 v1 v2))
      (coe MAlonzo.Code.Algebra.Structures.d2490
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.Structures.d2798
               (coe MAlonzo.Code.Algebra.d1422 v0))))
name528
  = "Algebra.Properties.BooleanAlgebra.XorRing.commutativeRing"
d528 v0 v1 v2 v3 v4 = du528 v2 v3 v4
du528 v0 v1 v2
  = coe MAlonzo.Code.Algebra.C309 erased erased v1
      (coe MAlonzo.Code.Algebra.d1414 v0)
      (coe MAlonzo.Code.Function.d68 erased erased)
      (coe MAlonzo.Code.Algebra.d1420 v0)
      (coe MAlonzo.Code.Algebra.d1418 v0)
      (coe du526 v0 v1 v2)
name530 = "Algebra.Properties.BooleanAlgebra._\8853_"
d530 v0 v1 v2
  = coe MAlonzo.Code.Algebra.d1414 v0
      (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
      (coe MAlonzo.Code.Algebra.d1416 v0
         (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))
name542
  = "Algebra.Properties.BooleanAlgebra.DefaultXorRing.commutativeRing"
d542 v0 v1 v2 = du542 v2
du542 v0
  = coe du528 v0
      (\ v1 v2 ->
         coe MAlonzo.Code.Algebra.d1414 v0
           (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
           (coe MAlonzo.Code.Algebra.d1416 v0
              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
      (\ v1 v2 ->
         coe MAlonzo.Code.Relation.Binary.Core.d516
           (coe MAlonzo.Code.Algebra.Structures.d2482
              (coe MAlonzo.Code.Algebra.Structures.d2630
                 (coe MAlonzo.Code.Algebra.Structures.d2798
                    (coe MAlonzo.Code.Algebra.d1422 v0))))
           (coe MAlonzo.Code.Algebra.d1414 v0
              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
              (coe MAlonzo.Code.Algebra.d1416 v0
                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
name544
  = "Algebra.Properties.BooleanAlgebra.DefaultXorRing.isCommutativeRing"
d544 v0 v1 v2 = du544 v2
du544 v0
  = coe du526 v0
      (\ v1 v2 ->
         coe MAlonzo.Code.Algebra.d1414 v0
           (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
           (coe MAlonzo.Code.Algebra.d1416 v0
              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
      (\ v1 v2 ->
         coe MAlonzo.Code.Relation.Binary.Core.d516
           (coe MAlonzo.Code.Algebra.Structures.d2482
              (coe MAlonzo.Code.Algebra.Structures.d2630
                 (coe MAlonzo.Code.Algebra.Structures.d2798
                    (coe MAlonzo.Code.Algebra.d1422 v0))))
           (coe MAlonzo.Code.Algebra.d1414 v0
              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
              (coe MAlonzo.Code.Algebra.d1416 v0
                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
name546
  = "Algebra.Properties.BooleanAlgebra.DefaultXorRing.\8853-annihilates-\172"
d546 v0 v1 v2 = du546 v2
du546 v0
  = coe d402 erased erased v0
      (\ v1 v2 ->
         coe MAlonzo.Code.Algebra.d1414 v0
           (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
           (coe MAlonzo.Code.Algebra.d1416 v0
              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
      (\ v1 v2 ->
         coe MAlonzo.Code.Relation.Binary.Core.d516
           (coe MAlonzo.Code.Algebra.Structures.d2482
              (coe MAlonzo.Code.Algebra.Structures.d2630
                 (coe MAlonzo.Code.Algebra.Structures.d2798
                    (coe MAlonzo.Code.Algebra.d1422 v0))))
           (coe MAlonzo.Code.Algebra.d1414 v0
              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
              (coe MAlonzo.Code.Algebra.d1416 v0
                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
name548
  = "Algebra.Properties.BooleanAlgebra.DefaultXorRing.\8853-\172-distrib\691"
d548 v0 v1 v2 = du548 v2
du548 v0
  = coe d392 erased erased v0
      (\ v1 v2 ->
         coe MAlonzo.Code.Algebra.d1414 v0
           (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
           (coe MAlonzo.Code.Algebra.d1416 v0
              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
      (\ v1 v2 ->
         coe MAlonzo.Code.Relation.Binary.Core.d516
           (coe MAlonzo.Code.Algebra.Structures.d2482
              (coe MAlonzo.Code.Algebra.Structures.d2630
                 (coe MAlonzo.Code.Algebra.Structures.d2798
                    (coe MAlonzo.Code.Algebra.d1422 v0))))
           (coe MAlonzo.Code.Algebra.d1414 v0
              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
              (coe MAlonzo.Code.Algebra.d1416 v0
                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))
name550
  = "Algebra.Properties.BooleanAlgebra.DefaultXorRing.\8853-\172-distrib\737"
d550 v0 v1 v2 = du550 v2
du550 v0
  = coe d362 erased erased v0
      (\ v1 v2 ->
         coe MAlonzo.Code.Algebra.d1414 v0
           (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
           (coe MAlonzo.Code.Algebra.d1416 v0
              (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2)))
      (\ v1 v2 ->
         coe MAlonzo.Code.Relation.Binary.Core.d516
           (coe MAlonzo.Code.Algebra.Structures.d2482
              (coe MAlonzo.Code.Algebra.Structures.d2630
                 (coe MAlonzo.Code.Algebra.Structures.d2798
                    (coe MAlonzo.Code.Algebra.d1422 v0))))
           (coe MAlonzo.Code.Algebra.d1414 v0
              (coe MAlonzo.Code.Algebra.d1412 v0 v1 v2)
              (coe MAlonzo.Code.Algebra.d1416 v0
                 (coe MAlonzo.Code.Algebra.d1414 v0 v1 v2))))