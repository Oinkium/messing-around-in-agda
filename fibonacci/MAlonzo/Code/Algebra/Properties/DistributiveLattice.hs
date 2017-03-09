{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.Properties.DistributiveLattice where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Algebra.Properties.Lattice
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Equivalence
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
name58 = "Algebra.Properties.DistributiveLattice.L.poset"
d58 v0 v1 v2 = du58 v2
du58 v0
  = coe MAlonzo.Code.Algebra.Properties.Lattice.du128
      (coe MAlonzo.Code.Algebra.C335 erased erased
         (coe MAlonzo.Code.Algebra.d1340 v0)
         (coe MAlonzo.Code.Algebra.d1342 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.d1344 v0)))
name60
  = "Algebra.Properties.DistributiveLattice.L.replace-equality"
d60 v0 v1 v2 = du60 v2
du60 v0
  = coe MAlonzo.Code.Algebra.Properties.Lattice.d164 erased erased
      (coe MAlonzo.Code.Algebra.C335 erased erased
         (coe MAlonzo.Code.Algebra.d1340 v0)
         (coe MAlonzo.Code.Algebra.d1342 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.d1344 v0)))
name62
  = "Algebra.Properties.DistributiveLattice.L.\8743-idempotent"
d62 v0 v1 v2 = du62 v2
du62 v0
  = coe MAlonzo.Code.Algebra.Properties.Lattice.d116 erased erased
      (coe MAlonzo.Code.Algebra.C335 erased erased
         (coe MAlonzo.Code.Algebra.d1340 v0)
         (coe MAlonzo.Code.Algebra.d1342 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.d1344 v0)))
name64
  = "Algebra.Properties.DistributiveLattice.L.\8743-\8744-isLattice"
d64 v0 v1 v2 = du64 v2
du64 v0
  = coe MAlonzo.Code.Algebra.Properties.Lattice.du124
      (coe MAlonzo.Code.Algebra.C335 erased erased
         (coe MAlonzo.Code.Algebra.d1340 v0)
         (coe MAlonzo.Code.Algebra.d1342 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.d1344 v0)))
name66
  = "Algebra.Properties.DistributiveLattice.L.\8743-\8744-lattice"
d66 v0 v1 v2 = du66 v2
du66 v0
  = coe MAlonzo.Code.Algebra.Properties.Lattice.du126
      (coe MAlonzo.Code.Algebra.C335 erased erased
         (coe MAlonzo.Code.Algebra.d1340 v0)
         (coe MAlonzo.Code.Algebra.d1342 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.d1344 v0)))
name68
  = "Algebra.Properties.DistributiveLattice.L.\8744-idempotent"
d68 v0 v1 v2 = du68 v2
du68 v0
  = coe MAlonzo.Code.Algebra.Properties.Lattice.d120 erased erased
      (coe MAlonzo.Code.Algebra.C335 erased erased
         (coe MAlonzo.Code.Algebra.d1340 v0)
         (coe MAlonzo.Code.Algebra.d1342 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.d1344 v0)))
name74
  = "Algebra.Properties.DistributiveLattice._._DistributesOver_"
d74 = erased
name120 = "Algebra.Properties.DistributiveLattice._._\8718"
d120 v0 v1 v2 = du120 v2
du120 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe MAlonzo.Code.Relation.Binary.C85 erased erased
         (coe MAlonzo.Code.Algebra.Structures.d2482
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.d1344 v0))))
name122
  = "Algebra.Properties.DistributiveLattice._._\8764\10216_\10217_"
d122 v0 v1 v2 = du122 v2
du122 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40
      (coe MAlonzo.Code.Relation.Binary.C85 erased erased
         (coe MAlonzo.Code.Algebra.Structures.d2482
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.d1344 v0))))
name136
  = "Algebra.Properties.DistributiveLattice.\8744-\8743-distrib"
d136 v0 v1 v2 = du136 v2
du136 v0
  = coe MAlonzo.Code.Data.Product.C30 (coe d142 erased erased v0)
      (coe MAlonzo.Code.Algebra.Structures.d2632
         (coe MAlonzo.Code.Algebra.d1344 v0))
name142
  = "Algebra.Properties.DistributiveLattice._.\8744-\8743-distrib\737"
d142 v0 v1 v2 v3 v4 v5 = du142 v2 v3 v4 v5
du142 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du122 v0
         (coe MAlonzo.Code.Algebra.d1340 v0 v1
            (coe MAlonzo.Code.Algebra.d1342 v0 v2 v3))
         (coe MAlonzo.Code.Algebra.d1340 v0
            (coe MAlonzo.Code.Algebra.d1342 v0 v2 v3)
            v1)
         (coe MAlonzo.Code.Algebra.d1342 v0
            (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d1340 v0 v1 v3))
         (coe MAlonzo.Code.Algebra.Structures.d2484
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.d1344 v0))
            v1
            (coe MAlonzo.Code.Algebra.d1342 v0 v2 v3))
         (coe du122 v0
            (coe MAlonzo.Code.Algebra.d1340 v0
               (coe MAlonzo.Code.Algebra.d1342 v0 v2 v3)
               v1)
            (coe MAlonzo.Code.Algebra.d1342 v0
               (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1)
               (coe MAlonzo.Code.Algebra.d1340 v0 v3 v1))
            (coe MAlonzo.Code.Algebra.d1342 v0
               (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1340 v0 v1 v3))
            (coe MAlonzo.Code.Algebra.Structures.d2632
               (coe MAlonzo.Code.Algebra.d1344 v0)
               v1
               v2
               v3)
            (coe du122 v0
               (coe MAlonzo.Code.Algebra.d1342 v0
                  (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.d1340 v0 v3 v1))
               (coe MAlonzo.Code.Algebra.d1342 v0
                  (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1340 v0 v1 v3))
               (coe MAlonzo.Code.Algebra.d1342 v0
                  (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1340 v0 v1 v3))
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Algebra.Structures.d2484
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.d1344 v0))
                     v2
                     v1)
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.d1344 v0))
                     (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1340 v0 v3 v1)
                     (coe MAlonzo.Code.Algebra.d1340 v0 v1 v3))
                  (coe MAlonzo.Code.Algebra.Structures.d2484
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.d1344 v0))
                     v3
                     v1))
               (coe du120 v0
                  (coe MAlonzo.Code.Algebra.d1342 v0
                     (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1340 v0 v1 v3))))))
name150
  = "Algebra.Properties.DistributiveLattice.\8743-\8744-distrib"
d150 v0 v1 v2 = du150 v2
du150 v0
  = coe MAlonzo.Code.Data.Product.C30 (coe d156 erased erased v0)
      (coe d164 erased erased v0)
name156
  = "Algebra.Properties.DistributiveLattice._.\8743-\8744-distrib\737"
d156 v0 v1 v2 v3 v4 v5 = du156 v2 v3 v4 v5
du156 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du122 v0
         (coe MAlonzo.Code.Algebra.d1342 v0 v1
            (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
         (coe MAlonzo.Code.Algebra.d1342 v0
            (coe MAlonzo.Code.Algebra.d1342 v0 v1
               (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2))
            (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
         (coe MAlonzo.Code.Algebra.d1340 v0
            (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.d1344 v0)))
               (coe MAlonzo.Code.Algebra.d1342 v0 v1
                  (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2))
               v1
               (coe MAlonzo.Code.Data.Product.d28
                  (coe MAlonzo.Code.Algebra.Structures.d2496
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.d1344 v0)))
                  v1
                  v2))
            (coe MAlonzo.Code.Algebra.Structures.d2494
               (coe MAlonzo.Code.Algebra.Structures.d2630
                  (coe MAlonzo.Code.Algebra.d1344 v0))
               v1
               (coe MAlonzo.Code.Algebra.d1342 v0 v1
                  (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3)
               (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
            (coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d2482
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.d1344 v0)))
               (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3)))
         (coe du122 v0
            (coe MAlonzo.Code.Algebra.d1342 v0
               (coe MAlonzo.Code.Algebra.d1342 v0 v1
                  (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.d1342 v0
               (coe MAlonzo.Code.Algebra.d1342 v0 v1
                  (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1))
               (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.d1340 v0
               (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Relation.Binary.Core.d516
                     (coe MAlonzo.Code.Algebra.Structures.d2482
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.d1344 v0)))
                     v1)
                  (coe MAlonzo.Code.Algebra.Structures.d2494
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.d1344 v0))
                     v1
                     v1
                     (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1))
                  (coe MAlonzo.Code.Algebra.Structures.d2484
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.d1344 v0))
                     v1
                     v2))
               (coe MAlonzo.Code.Algebra.Structures.d2494
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.d1344 v0))
                  (coe MAlonzo.Code.Algebra.d1342 v0 v1
                     (coe MAlonzo.Code.Algebra.d1340 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.d1342 v0 v1
                     (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1))
                  (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.d1344 v0)))
                  (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3)))
            (coe du122 v0
               (coe MAlonzo.Code.Algebra.d1342 v0
                  (coe MAlonzo.Code.Algebra.d1342 v0 v1
                     (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1))
                  (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
               (coe MAlonzo.Code.Algebra.d1342 v0 v1
                  (coe MAlonzo.Code.Algebra.d1342 v0
                     (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3)))
               (coe MAlonzo.Code.Algebra.d1340 v0
                  (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
               (coe MAlonzo.Code.Algebra.Structures.d2492
                  (coe MAlonzo.Code.Algebra.Structures.d2630
                     (coe MAlonzo.Code.Algebra.d1344 v0))
                  v1
                  (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
               (coe du122 v0
                  (coe MAlonzo.Code.Algebra.d1342 v0 v1
                     (coe MAlonzo.Code.Algebra.d1342 v0
                        (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1)
                        (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3)))
                  (coe MAlonzo.Code.Algebra.d1342 v0 v1
                     (coe MAlonzo.Code.Algebra.d1340 v0 v2
                        (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3)))
                  (coe MAlonzo.Code.Algebra.d1340 v0
                     (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.d1344 v0)))
                        v1)
                     (coe MAlonzo.Code.Algebra.Structures.d2494
                        (coe MAlonzo.Code.Algebra.Structures.d2630
                           (coe MAlonzo.Code.Algebra.d1344 v0))
                        v1
                        v1
                        (coe MAlonzo.Code.Algebra.d1342 v0
                           (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1)
                           (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
                        (coe MAlonzo.Code.Algebra.d1340 v0 v2
                           (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3)))
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d2482
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.d1344 v0)))
                        (coe MAlonzo.Code.Algebra.d1340 v0 v2
                           (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                        (coe MAlonzo.Code.Algebra.d1342 v0
                           (coe MAlonzo.Code.Algebra.d1340 v0 v2 v1)
                           (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
                        (coe MAlonzo.Code.Data.Product.d26 (coe du136 v0) v2 v1 v3)))
                  (coe du122 v0
                     (coe MAlonzo.Code.Algebra.d1342 v0 v1
                        (coe MAlonzo.Code.Algebra.d1340 v0 v2
                           (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3)))
                     (coe MAlonzo.Code.Algebra.d1342 v0
                        (coe MAlonzo.Code.Algebra.d1340 v0 v1
                           (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                        (coe MAlonzo.Code.Algebra.d1340 v0 v2
                           (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3)))
                     (coe MAlonzo.Code.Algebra.d1340 v0
                        (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Relation.Binary.Core.d518
                           (coe MAlonzo.Code.Algebra.Structures.d2482
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.d1344 v0)))
                           (coe MAlonzo.Code.Algebra.d1340 v0 v1
                              (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                           v1
                           (coe MAlonzo.Code.Data.Product.d26
                              (coe MAlonzo.Code.Algebra.Structures.d2496
                                 (coe MAlonzo.Code.Algebra.Structures.d2630
                                    (coe MAlonzo.Code.Algebra.d1344 v0)))
                              v1
                              v3))
                        (coe MAlonzo.Code.Algebra.Structures.d2494
                           (coe MAlonzo.Code.Algebra.Structures.d2630
                              (coe MAlonzo.Code.Algebra.d1344 v0))
                           v1
                           (coe MAlonzo.Code.Algebra.d1340 v0 v1
                              (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                           (coe MAlonzo.Code.Algebra.d1340 v0 v2
                              (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                           (coe MAlonzo.Code.Algebra.d1340 v0 v2
                              (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3)))
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe MAlonzo.Code.Algebra.Structures.d2482
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.d1344 v0)))
                           (coe MAlonzo.Code.Algebra.d1340 v0 v2
                              (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))))
                     (coe du122 v0
                        (coe MAlonzo.Code.Algebra.d1342 v0
                           (coe MAlonzo.Code.Algebra.d1340 v0 v1
                              (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                           (coe MAlonzo.Code.Algebra.d1340 v0 v2
                              (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3)))
                        (coe MAlonzo.Code.Algebra.d1340 v0
                           (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                        (coe MAlonzo.Code.Algebra.d1340 v0
                           (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                        (coe MAlonzo.Code.Function.du158
                           (coe MAlonzo.Code.Relation.Binary.Core.d518
                              (coe MAlonzo.Code.Algebra.Structures.d2482
                                 (coe MAlonzo.Code.Algebra.Structures.d2630
                                    (coe MAlonzo.Code.Algebra.d1344 v0)))
                              (coe MAlonzo.Code.Algebra.d1340 v0
                                 (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
                                 (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                              (coe MAlonzo.Code.Algebra.d1342 v0
                                 (coe MAlonzo.Code.Algebra.d1340 v0 v1
                                    (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
                                 (coe MAlonzo.Code.Algebra.d1340 v0 v2
                                    (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))))
                           (coe MAlonzo.Code.Data.Product.d28 (coe du136 v0)
                              (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3)
                              v1
                              v2))
                        (coe du120 v0
                           (coe MAlonzo.Code.Algebra.d1340 v0
                              (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
                              (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3)))))))))
name164
  = "Algebra.Properties.DistributiveLattice._.\8743-\8744-distrib\691"
d164 v0 v1 v2 v3 v4 v5 = du164 v2 v3 v4 v5
du164 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du122 v0
         (coe MAlonzo.Code.Algebra.d1342 v0
            (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3)
            v1)
         (coe MAlonzo.Code.Algebra.d1342 v0 v1
            (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
         (coe MAlonzo.Code.Algebra.d1340 v0
            (coe MAlonzo.Code.Algebra.d1342 v0 v2 v1)
            (coe MAlonzo.Code.Algebra.d1342 v0 v3 v1))
         (coe MAlonzo.Code.Algebra.Structures.d2490
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.d1344 v0))
            (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3)
            v1)
         (coe du122 v0
            (coe MAlonzo.Code.Algebra.d1342 v0 v1
               (coe MAlonzo.Code.Algebra.d1340 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.d1340 v0
               (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
            (coe MAlonzo.Code.Algebra.d1340 v0
               (coe MAlonzo.Code.Algebra.d1342 v0 v2 v1)
               (coe MAlonzo.Code.Algebra.d1342 v0 v3 v1))
            (coe du156 v0 v1 v2 v3)
            (coe du122 v0
               (coe MAlonzo.Code.Algebra.d1340 v0
                  (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3))
               (coe MAlonzo.Code.Algebra.d1340 v0
                  (coe MAlonzo.Code.Algebra.d1342 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.d1342 v0 v3 v1))
               (coe MAlonzo.Code.Algebra.d1340 v0
                  (coe MAlonzo.Code.Algebra.d1342 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.d1342 v0 v3 v1))
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Algebra.Structures.d2490
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.d1344 v0))
                     v1
                     v2)
                  (coe MAlonzo.Code.Algebra.Structures.d2488
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.d1344 v0))
                     (coe MAlonzo.Code.Algebra.d1342 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1342 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.d1342 v0 v1 v3)
                     (coe MAlonzo.Code.Algebra.d1342 v0 v3 v1))
                  (coe MAlonzo.Code.Algebra.Structures.d2490
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.d1344 v0))
                     v1
                     v3))
               (coe du120 v0
                  (coe MAlonzo.Code.Algebra.d1340 v0
                     (coe MAlonzo.Code.Algebra.d1342 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.d1342 v0 v3 v1))))))
name172
  = "Algebra.Properties.DistributiveLattice.\8743-\8744-isDistributiveLattice"
d172 v0 v1 v2 = du172 v2
du172 v0
  = coe MAlonzo.Code.Algebra.Structures.C573 (coe du64 v0)
      (coe MAlonzo.Code.Data.Product.d28 (coe du150 v0))
name174
  = "Algebra.Properties.DistributiveLattice.\8743-\8744-distributiveLattice"
d174 v0 v1 v2 = du174 v2
du174 v0
  = coe MAlonzo.Code.Algebra.C355 erased erased
      (coe MAlonzo.Code.Algebra.d1342 v0)
      (coe MAlonzo.Code.Algebra.d1340 v0)
      (coe du172 v0)
name182 = "Algebra.Properties.DistributiveLattice.replace-equality"
d182 v0 v1 v2 v3 v4 = du182 v2 v3 v4
du182 v0 v1 v2
  = coe MAlonzo.Code.Algebra.C355 erased v1
      (coe MAlonzo.Code.Algebra.d1340 v0)
      (coe MAlonzo.Code.Algebra.d1342 v0)
      (coe MAlonzo.Code.Algebra.Structures.C573
         (coe MAlonzo.Code.Algebra.d1286 (coe du60 v0 v1 v2))
         (\ v3 v4 v5 ->
            coe MAlonzo.Code.Function.Equality.d38
              (coe MAlonzo.Code.Function.Equivalence.d34
                 (coe v2
                    (coe MAlonzo.Code.Algebra.d1340 v0
                       (coe MAlonzo.Code.Algebra.d1342 v0 v4 v5)
                       v3)
                    (coe MAlonzo.Code.Algebra.d1342 v0
                       (coe MAlonzo.Code.Algebra.d1340 v0 v4 v3)
                       (coe MAlonzo.Code.Algebra.d1340 v0 v5 v3))))
              (coe MAlonzo.Code.Algebra.Structures.d2632
                 (coe MAlonzo.Code.Algebra.d1344 v0)
                 v3
                 v4
                 v5)))
name200 = "Algebra.Properties.DistributiveLattice._.E.to"
d200 v0 v1 v2 v3 v4 = du200 v2 v3 v4
du200 v0 v1 v2
  = coe MAlonzo.Code.Function.Equivalence.d34 (coe v0 v1 v2)