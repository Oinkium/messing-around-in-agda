{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.Properties.Lattice where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Equivalence
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
name100 = "Algebra.Properties.Lattice._._\8718"
d100 v0 v1 v2 = du100 v2
du100 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe MAlonzo.Code.Relation.Binary.C85 erased erased
         (coe MAlonzo.Code.Algebra.Structures.d2482
            (coe MAlonzo.Code.Algebra.d1286 v0)))
name102 = "Algebra.Properties.Lattice._._\8764\10216_\10217_"
d102 v0 v1 v2 = du102 v2
du102 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40
      (coe MAlonzo.Code.Relation.Binary.C85 erased erased
         (coe MAlonzo.Code.Algebra.Structures.d2482
            (coe MAlonzo.Code.Algebra.d1286 v0)))
name116 = "Algebra.Properties.Lattice.\8743-idempotent"
d116 v0 v1 v2 v3 = du116 v2 v3
du116 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du102 v0 (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1)
         (coe MAlonzo.Code.Algebra.d1284 v0 v1
            (coe MAlonzo.Code.Algebra.d1282 v0 v1
               (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1)))
         v1
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.d1286 v0))
               v1)
            (coe MAlonzo.Code.Algebra.Structures.d2494
               (coe MAlonzo.Code.Algebra.d1286 v0)
               v1
               v1
               v1
               (coe MAlonzo.Code.Algebra.d1282 v0 v1
                  (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1)))
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.d1286 v0))
               (coe MAlonzo.Code.Algebra.d1282 v0 v1
                  (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1))
               v1
               (coe MAlonzo.Code.Data.Product.d26
                  (coe MAlonzo.Code.Algebra.Structures.d2496
                     (coe MAlonzo.Code.Algebra.d1286 v0))
                  v1
                  v1)))
         (coe du102 v0
            (coe MAlonzo.Code.Algebra.d1284 v0 v1
               (coe MAlonzo.Code.Algebra.d1282 v0 v1
                  (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1)))
            v1
            v1
            (coe MAlonzo.Code.Data.Product.d28
               (coe MAlonzo.Code.Algebra.Structures.d2496
                  (coe MAlonzo.Code.Algebra.d1286 v0))
               v1
               (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1))
            (coe du100 v0 v1)))
name120 = "Algebra.Properties.Lattice.\8744-idempotent"
d120 v0 v1 v2 v3 = du120 v2 v3
du120 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du102 v0 (coe MAlonzo.Code.Algebra.d1282 v0 v1 v1)
         (coe MAlonzo.Code.Algebra.d1282 v0 v1
            (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1))
         v1
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.d1286 v0))
               v1)
            (coe MAlonzo.Code.Algebra.Structures.d2488
               (coe MAlonzo.Code.Algebra.d1286 v0)
               v1
               v1
               v1
               (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1))
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.d1286 v0))
               (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1)
               v1
               (coe du116 v0 v1)))
         (coe du102 v0
            (coe MAlonzo.Code.Algebra.d1282 v0 v1
               (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1))
            v1
            v1
            (coe MAlonzo.Code.Data.Product.d26
               (coe MAlonzo.Code.Algebra.Structures.d2496
                  (coe MAlonzo.Code.Algebra.d1286 v0))
               v1
               v1)
            (coe du100 v0 v1)))
name124 = "Algebra.Properties.Lattice.\8743-\8744-isLattice"
d124 v0 v1 v2 = du124 v2
du124 v0
  = coe MAlonzo.Code.Algebra.Structures.C539
      (coe MAlonzo.Code.Algebra.Structures.d2482
         (coe MAlonzo.Code.Algebra.d1286 v0))
      (coe MAlonzo.Code.Algebra.Structures.d2490
         (coe MAlonzo.Code.Algebra.d1286 v0))
      (coe MAlonzo.Code.Algebra.Structures.d2492
         (coe MAlonzo.Code.Algebra.d1286 v0))
      (coe MAlonzo.Code.Algebra.Structures.d2494
         (coe MAlonzo.Code.Algebra.d1286 v0))
      (coe MAlonzo.Code.Algebra.Structures.d2484
         (coe MAlonzo.Code.Algebra.d1286 v0))
      (coe MAlonzo.Code.Algebra.Structures.d2486
         (coe MAlonzo.Code.Algebra.d1286 v0))
      (coe MAlonzo.Code.Algebra.Structures.d2488
         (coe MAlonzo.Code.Algebra.d1286 v0))
      (coe MAlonzo.Code.Data.Product.du250
         (coe MAlonzo.Code.Algebra.Structures.d2496
            (coe MAlonzo.Code.Algebra.d1286 v0)))
name126 = "Algebra.Properties.Lattice.\8743-\8744-lattice"
d126 v0 v1 v2 = du126 v2
du126 v0
  = coe MAlonzo.Code.Algebra.C335 erased erased
      (coe MAlonzo.Code.Algebra.d1284 v0)
      (coe MAlonzo.Code.Algebra.d1282 v0)
      (coe du124 v0)
name128 = "Algebra.Properties.Lattice.poset"
d128 v0 v1 v2 = du128 v2
du128 v0
  = coe MAlonzo.Code.Relation.Binary.C235 erased erased erased
      (coe MAlonzo.Code.Relation.Binary.C217
         (coe MAlonzo.Code.Relation.Binary.C17
            (coe MAlonzo.Code.Algebra.Structures.d2482
               (coe MAlonzo.Code.Algebra.d1286 v0))
            (\ v1 v2 v3 ->
               coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                 (coe du102 v0 v1 (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1)
                    (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                    (coe MAlonzo.Code.Function.du158
                       (coe MAlonzo.Code.Relation.Binary.Core.d518
                          (coe MAlonzo.Code.Algebra.Structures.d2482
                             (coe MAlonzo.Code.Algebra.d1286 v0))
                          (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1)
                          v1)
                       (coe du116 v0 v1))
                    (coe du102 v0 (coe MAlonzo.Code.Algebra.d1284 v0 v1 v1)
                       (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                       (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                       (coe MAlonzo.Code.Algebra.Structures.d2494
                          (coe MAlonzo.Code.Algebra.d1286 v0)
                          v1
                          v1
                          v1
                          v2
                          (coe MAlonzo.Code.Relation.Binary.Core.d516
                             (coe MAlonzo.Code.Algebra.Structures.d2482
                                (coe MAlonzo.Code.Algebra.d1286 v0))
                             v1)
                          v3)
                       (coe du100 v0 (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)))))
            (\ v1 v2 v3 v4 v5 ->
               coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                 (coe du102 v0 v1 (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                    (coe MAlonzo.Code.Algebra.d1284 v0 v1 v3)
                    v4
                    (coe du102 v0 (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                       (coe MAlonzo.Code.Algebra.d1284 v0 v1
                          (coe MAlonzo.Code.Algebra.d1284 v0 v2 v3))
                       (coe MAlonzo.Code.Algebra.d1284 v0 v1 v3)
                       (coe MAlonzo.Code.Algebra.Structures.d2494
                          (coe MAlonzo.Code.Algebra.d1286 v0)
                          v1
                          v1
                          v2
                          (coe MAlonzo.Code.Algebra.d1284 v0 v2 v3)
                          (coe MAlonzo.Code.Relation.Binary.Core.d516
                             (coe MAlonzo.Code.Algebra.Structures.d2482
                                (coe MAlonzo.Code.Algebra.d1286 v0))
                             v1)
                          v5)
                       (coe du102 v0
                          (coe MAlonzo.Code.Algebra.d1284 v0 v1
                             (coe MAlonzo.Code.Algebra.d1284 v0 v2 v3))
                          (coe MAlonzo.Code.Algebra.d1284 v0
                             (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                             v3)
                          (coe MAlonzo.Code.Algebra.d1284 v0 v1 v3)
                          (coe MAlonzo.Code.Relation.Binary.Core.d518
                             (coe MAlonzo.Code.Algebra.Structures.d2482
                                (coe MAlonzo.Code.Algebra.d1286 v0))
                             (coe MAlonzo.Code.Algebra.d1284 v0
                                (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                                v3)
                             (coe MAlonzo.Code.Algebra.d1284 v0 v1
                                (coe MAlonzo.Code.Algebra.d1284 v0 v2 v3))
                             (coe MAlonzo.Code.Algebra.Structures.d2492
                                (coe MAlonzo.Code.Algebra.d1286 v0)
                                v1
                                v2
                                v3))
                          (coe du102 v0
                             (coe MAlonzo.Code.Algebra.d1284 v0
                                (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                                v3)
                             (coe MAlonzo.Code.Algebra.d1284 v0 v1 v3)
                             (coe MAlonzo.Code.Algebra.d1284 v0 v1 v3)
                             (coe MAlonzo.Code.Algebra.Structures.d2494
                                (coe MAlonzo.Code.Algebra.d1286 v0)
                                (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                                v1
                                v3
                                v3
                                (coe MAlonzo.Code.Relation.Binary.Core.d518
                                   (coe MAlonzo.Code.Algebra.Structures.d2482
                                      (coe MAlonzo.Code.Algebra.d1286 v0))
                                   v1
                                   (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                                   v4)
                                (coe MAlonzo.Code.Relation.Binary.Core.d516
                                   (coe MAlonzo.Code.Algebra.Structures.d2482
                                      (coe MAlonzo.Code.Algebra.d1286 v0))
                                   v3))
                             (coe du100 v0 (coe MAlonzo.Code.Algebra.d1284 v0 v1 v3))))))))
         (\ v1 v2 v3 v4 ->
            coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
              (coe du102 v0 v1 (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2) v2 v3
                 (coe du102 v0 (coe MAlonzo.Code.Algebra.d1284 v0 v1 v2)
                    (coe MAlonzo.Code.Algebra.d1284 v0 v2 v1)
                    v2
                    (coe MAlonzo.Code.Algebra.Structures.d2490
                       (coe MAlonzo.Code.Algebra.d1286 v0)
                       v1
                       v2)
                    (coe du102 v0 (coe MAlonzo.Code.Algebra.d1284 v0 v2 v1) v2 v2
                       (coe MAlonzo.Code.Relation.Binary.Core.d518
                          (coe MAlonzo.Code.Algebra.Structures.d2482
                             (coe MAlonzo.Code.Algebra.d1286 v0))
                          v2
                          (coe MAlonzo.Code.Algebra.d1284 v0 v2 v1)
                          v4)
                       (coe du100 v0 v2))))))
name164 = "Algebra.Properties.Lattice.replace-equality"
d164 v0 v1 v2 v3 v4 = du164 v2 v3 v4
du164 v0 v1 v2
  = coe MAlonzo.Code.Algebra.C335 erased v1
      (coe MAlonzo.Code.Algebra.d1282 v0)
      (coe MAlonzo.Code.Algebra.d1284 v0)
      (coe MAlonzo.Code.Algebra.Structures.C539
         (coe MAlonzo.Code.Relation.Binary.Core.C605
            (\ v3 ->
               coe MAlonzo.Code.Function.Equality.d38
                 (coe MAlonzo.Code.Function.Equivalence.d34 (coe v2 v3 v3))
                 (coe MAlonzo.Code.Relation.Binary.Core.d516
                    (coe MAlonzo.Code.Algebra.Structures.d2482
                       (coe MAlonzo.Code.Algebra.d1286 v0))
                    v3))
            (\ v3 v4 v5 ->
               coe MAlonzo.Code.Function.Equality.d38
                 (coe MAlonzo.Code.Function.Equivalence.d34 (coe v2 v4 v3))
                 (coe MAlonzo.Code.Relation.Binary.Core.d518
                    (coe MAlonzo.Code.Algebra.Structures.d2482
                       (coe MAlonzo.Code.Algebra.d1286 v0))
                    v3
                    v4
                    (coe MAlonzo.Code.Function.Equality.d38
                       (coe MAlonzo.Code.Function.Equivalence.d36 (coe v2 v3 v4))
                       v5)))
            (\ v3 v4 v5 v6 v7 ->
               coe MAlonzo.Code.Function.Equality.d38
                 (coe MAlonzo.Code.Function.Equivalence.d34 (coe v2 v3 v5))
                 (coe MAlonzo.Code.Relation.Binary.Core.d520
                    (coe MAlonzo.Code.Algebra.Structures.d2482
                       (coe MAlonzo.Code.Algebra.d1286 v0))
                    v3
                    v4
                    v5
                    (coe MAlonzo.Code.Function.Equality.d38
                       (coe MAlonzo.Code.Function.Equivalence.d36 (coe v2 v3 v4))
                       v6)
                    (coe MAlonzo.Code.Function.Equality.d38
                       (coe MAlonzo.Code.Function.Equivalence.d36 (coe v2 v4 v5))
                       v7))))
         (\ v3 v4 ->
            coe MAlonzo.Code.Function.Equality.d38
              (coe MAlonzo.Code.Function.Equivalence.d34
                 (coe v2 (coe MAlonzo.Code.Algebra.d1282 v0 v3 v4)
                    (coe MAlonzo.Code.Algebra.d1282 v0 v4 v3)))
              (coe MAlonzo.Code.Algebra.Structures.d2484
                 (coe MAlonzo.Code.Algebra.d1286 v0)
                 v3
                 v4))
         (\ v3 v4 v5 ->
            coe MAlonzo.Code.Function.Equality.d38
              (coe MAlonzo.Code.Function.Equivalence.d34
                 (coe v2
                    (coe MAlonzo.Code.Algebra.d1282 v0
                       (coe MAlonzo.Code.Algebra.d1282 v0 v3 v4)
                       v5)
                    (coe MAlonzo.Code.Algebra.d1282 v0 v3
                       (coe MAlonzo.Code.Algebra.d1282 v0 v4 v5))))
              (coe MAlonzo.Code.Algebra.Structures.d2486
                 (coe MAlonzo.Code.Algebra.d1286 v0)
                 v3
                 v4
                 v5))
         (\ v3 v4 v5 v6 v7 v8 ->
            coe MAlonzo.Code.Function.Equality.d38
              (coe MAlonzo.Code.Function.Equivalence.d34
                 (coe v2 (coe MAlonzo.Code.Algebra.d1282 v0 v3 v5)
                    (coe MAlonzo.Code.Algebra.d1282 v0 v4 v6)))
              (coe MAlonzo.Code.Algebra.Structures.d2488
                 (coe MAlonzo.Code.Algebra.d1286 v0)
                 v3
                 v4
                 v5
                 v6
                 (coe MAlonzo.Code.Function.Equality.d38
                    (coe MAlonzo.Code.Function.Equivalence.d36 (coe v2 v3 v4))
                    v7)
                 (coe MAlonzo.Code.Function.Equality.d38
                    (coe MAlonzo.Code.Function.Equivalence.d36 (coe v2 v5 v6))
                    v8)))
         (\ v3 v4 ->
            coe MAlonzo.Code.Function.Equality.d38
              (coe MAlonzo.Code.Function.Equivalence.d34
                 (coe v2 (coe MAlonzo.Code.Algebra.d1284 v0 v3 v4)
                    (coe MAlonzo.Code.Algebra.d1284 v0 v4 v3)))
              (coe MAlonzo.Code.Algebra.Structures.d2490
                 (coe MAlonzo.Code.Algebra.d1286 v0)
                 v3
                 v4))
         (\ v3 v4 v5 ->
            coe MAlonzo.Code.Function.Equality.d38
              (coe MAlonzo.Code.Function.Equivalence.d34
                 (coe v2
                    (coe MAlonzo.Code.Algebra.d1284 v0
                       (coe MAlonzo.Code.Algebra.d1284 v0 v3 v4)
                       v5)
                    (coe MAlonzo.Code.Algebra.d1284 v0 v3
                       (coe MAlonzo.Code.Algebra.d1284 v0 v4 v5))))
              (coe MAlonzo.Code.Algebra.Structures.d2492
                 (coe MAlonzo.Code.Algebra.d1286 v0)
                 v3
                 v4
                 v5))
         (\ v3 v4 v5 v6 v7 v8 ->
            coe MAlonzo.Code.Function.Equality.d38
              (coe MAlonzo.Code.Function.Equivalence.d34
                 (coe v2 (coe MAlonzo.Code.Algebra.d1284 v0 v3 v5)
                    (coe MAlonzo.Code.Algebra.d1284 v0 v4 v6)))
              (coe MAlonzo.Code.Algebra.Structures.d2494
                 (coe MAlonzo.Code.Algebra.d1286 v0)
                 v3
                 v4
                 v5
                 v6
                 (coe MAlonzo.Code.Function.Equality.d38
                    (coe MAlonzo.Code.Function.Equivalence.d36 (coe v2 v3 v4))
                    v7)
                 (coe MAlonzo.Code.Function.Equality.d38
                    (coe MAlonzo.Code.Function.Equivalence.d36 (coe v2 v5 v6))
                    v8)))
         (coe MAlonzo.Code.Data.Product.C30
            (\ v3 v4 ->
               coe MAlonzo.Code.Function.Equality.d38
                 (coe MAlonzo.Code.Function.Equivalence.d34
                    (coe v2
                       (coe MAlonzo.Code.Algebra.d1282 v0 v3
                          (coe MAlonzo.Code.Algebra.d1284 v0 v3 v4))
                       v3))
                 (coe MAlonzo.Code.Data.Product.d26
                    (coe MAlonzo.Code.Algebra.Structures.d2496
                       (coe MAlonzo.Code.Algebra.d1286 v0))
                    v3
                    v4))
            (\ v3 v4 ->
               coe MAlonzo.Code.Function.Equality.d38
                 (coe MAlonzo.Code.Function.Equivalence.d34
                    (coe v2
                       (coe MAlonzo.Code.Algebra.d1284 v0 v3
                          (coe MAlonzo.Code.Algebra.d1282 v0 v3 v4))
                       v3))
                 (coe MAlonzo.Code.Data.Product.d28
                    (coe MAlonzo.Code.Algebra.Structures.d2496
                       (coe MAlonzo.Code.Algebra.d1286 v0))
                    v3
                    v4))))
name180 = "Algebra.Properties.Lattice._.E.from"
d180 v0 v1 v2 v3 v4 = du180 v2 v3 v4
du180 v0 v1 v2
  = coe MAlonzo.Code.Function.Equivalence.d36 (coe v0 v1 v2)
name182 = "Algebra.Properties.Lattice._.E.to"
d182 v0 v1 v2 v3 v4 = du182 v2 v3 v4
du182 v0 v1 v2
  = coe MAlonzo.Code.Function.Equivalence.d34 (coe v0 v1 v2)