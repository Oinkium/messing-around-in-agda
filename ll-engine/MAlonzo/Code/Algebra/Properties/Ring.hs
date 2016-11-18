{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.Properties.Ring where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.Properties.AbelianGroup
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
name108 = "Algebra.Properties.Ring._.setoid"
d108 v0 v1 v2 = du108 v2
du108 v0 = coe MAlonzo.Code.Algebra.du1098 v0
name114 = "Algebra.Properties.Ring._.zero"
d114 v0 v1 v2 = du114 v2
du114 v0 = coe MAlonzo.Code.Algebra.du1070 v0
name120 = "Algebra.Properties.Ring._._\8718"
d120 v0 v1 v2 = du120 v2
du120 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe du108 v0)
name122 = "Algebra.Properties.Ring._._\8764\10216_\10217_"
d122 v0 v1 v2 = du122 v2
du122 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40 (coe du108 v0)
name138 = "Algebra.Properties.Ring._.identity-unique"
d138 v0 v1 v2 = du138 v2
du138 v0
  = coe MAlonzo.Code.Algebra.Properties.AbelianGroup.du92
      (coe MAlonzo.Code.Algebra.C103 erased erased
         (coe MAlonzo.Code.Algebra.d1002 v0)
         (coe MAlonzo.Code.Algebra.d1008 v0)
         (coe MAlonzo.Code.Algebra.d1006 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.d1012 v0)))
name140 = "Algebra.Properties.Ring._.left-identity-unique"
d140 v0 v1 v2 = du140 v2
du140 v0
  = coe MAlonzo.Code.Algebra.Properties.AbelianGroup.du94
      (coe MAlonzo.Code.Algebra.C103 erased erased
         (coe MAlonzo.Code.Algebra.d1002 v0)
         (coe MAlonzo.Code.Algebra.d1008 v0)
         (coe MAlonzo.Code.Algebra.d1006 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.d1012 v0)))
name142 = "Algebra.Properties.Ring._.left-inverse-unique"
d142 v0 v1 v2 = du142 v2
du142 v0
  = coe MAlonzo.Code.Algebra.Properties.AbelianGroup.du96
      (coe MAlonzo.Code.Algebra.C103 erased erased
         (coe MAlonzo.Code.Algebra.d1002 v0)
         (coe MAlonzo.Code.Algebra.d1008 v0)
         (coe MAlonzo.Code.Algebra.d1006 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.d1012 v0)))
name144 = "Algebra.Properties.Ring._.right-identity-unique"
d144 v0 v1 v2 = du144 v2
du144 v0
  = coe MAlonzo.Code.Algebra.Properties.AbelianGroup.du98
      (coe MAlonzo.Code.Algebra.C103 erased erased
         (coe MAlonzo.Code.Algebra.d1002 v0)
         (coe MAlonzo.Code.Algebra.d1008 v0)
         (coe MAlonzo.Code.Algebra.d1006 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.d1012 v0)))
name146 = "Algebra.Properties.Ring._.right-inverse-unique"
d146 v0 v1 v2 = du146 v2
du146 v0
  = coe MAlonzo.Code.Algebra.Properties.AbelianGroup.du100
      (coe MAlonzo.Code.Algebra.C103 erased erased
         (coe MAlonzo.Code.Algebra.d1002 v0)
         (coe MAlonzo.Code.Algebra.d1008 v0)
         (coe MAlonzo.Code.Algebra.d1006 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.d1012 v0)))
name148 = "Algebra.Properties.Ring._.\8315\185-\8729-comm"
d148 v0 v1 v2 = du148 v2
du148 v0
  = coe MAlonzo.Code.Algebra.Properties.AbelianGroup.d118 erased
      erased
      (coe MAlonzo.Code.Algebra.C103 erased erased
         (coe MAlonzo.Code.Algebra.d1002 v0)
         (coe MAlonzo.Code.Algebra.d1008 v0)
         (coe MAlonzo.Code.Algebra.d1006 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.d1012 v0)))
name150 = "Algebra.Properties.Ring._.\8315\185-involutive"
d150 v0 v1 v2 = du150 v2
du150 v0
  = coe MAlonzo.Code.Algebra.Properties.AbelianGroup.du102
      (coe MAlonzo.Code.Algebra.C103 erased erased
         (coe MAlonzo.Code.Algebra.d1002 v0)
         (coe MAlonzo.Code.Algebra.d1008 v0)
         (coe MAlonzo.Code.Algebra.d1006 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.d1012 v0)))
name156 = "Algebra.Properties.Ring.-\8255*-distrib\737"
d156 v0 v1 v2 v3 v4 = du156 v2 v3 v4
du156 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du122 v0
         (coe MAlonzo.Code.Algebra.d1004 v0
            (coe MAlonzo.Code.Algebra.d1006 v0 v1)
            v2)
         (coe MAlonzo.Code.Algebra.d1002 v0
            (coe MAlonzo.Code.Algebra.d1004 v0
               (coe MAlonzo.Code.Algebra.d1006 v0 v1)
               v2)
            (coe MAlonzo.Code.Algebra.d1008 v0))
         (coe MAlonzo.Code.Algebra.d1006 v0
            (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d124
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.Structures.d746
                           (coe MAlonzo.Code.Algebra.Structures.d2050
                              (coe MAlonzo.Code.Algebra.d1012 v0))))))
               (coe MAlonzo.Code.Algebra.d1002 v0
                  (coe MAlonzo.Code.Algebra.d1004 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1008 v0))
               (coe MAlonzo.Code.Algebra.d1004 v0
                  (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                  v2))
            (coe MAlonzo.Code.Data.Product.d28
               (coe MAlonzo.Code.Algebra.Structures.d264
                  (coe MAlonzo.Code.Algebra.Structures.d588
                     (coe MAlonzo.Code.Algebra.Structures.d746
                        (coe MAlonzo.Code.Algebra.Structures.d2050
                           (coe MAlonzo.Code.Algebra.d1012 v0)))))
               (coe MAlonzo.Code.Algebra.d1004 v0
                  (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                  v2)))
         (coe du122 v0
            (coe MAlonzo.Code.Algebra.d1002 v0
               (coe MAlonzo.Code.Algebra.d1004 v0
                  (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                  v2)
               (coe MAlonzo.Code.Algebra.d1008 v0))
            (coe MAlonzo.Code.Algebra.d1002 v0
               (coe MAlonzo.Code.Algebra.d1004 v0
                  (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                  v2)
               (coe MAlonzo.Code.Algebra.d1002 v0
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1006 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))))
            (coe MAlonzo.Code.Algebra.d1006 v0
               (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.Structures.d746
                              (coe MAlonzo.Code.Algebra.Structures.d2050
                                 (coe MAlonzo.Code.Algebra.d1012 v0))))))
                  (coe MAlonzo.Code.Algebra.d1004 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                     v2))
               (coe MAlonzo.Code.Algebra.Structures.d128
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.Structures.d746
                           (coe MAlonzo.Code.Algebra.Structures.d2050
                              (coe MAlonzo.Code.Algebra.d1012 v0)))))
                  (coe MAlonzo.Code.Algebra.d1004 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1004 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1008 v0)
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))))
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.Structures.d746
                              (coe MAlonzo.Code.Algebra.Structures.d2050
                                 (coe MAlonzo.Code.Algebra.d1012 v0))))))
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                  (coe MAlonzo.Code.Algebra.d1008 v0)
                  (coe MAlonzo.Code.Data.Product.d28
                     (coe MAlonzo.Code.Algebra.Structures.d590
                        (coe MAlonzo.Code.Algebra.Structures.d746
                           (coe MAlonzo.Code.Algebra.Structures.d2050
                              (coe MAlonzo.Code.Algebra.d1012 v0))))
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))))
            (coe du122 v0
               (coe MAlonzo.Code.Algebra.d1002 v0
                  (coe MAlonzo.Code.Algebra.d1004 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                     v2)
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))))
               (coe MAlonzo.Code.Algebra.d1002 v0
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0
                        (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.d1006 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
               (coe MAlonzo.Code.Algebra.d1006 v0
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d124
                        (coe MAlonzo.Code.Algebra.Structures.d262
                           (coe MAlonzo.Code.Algebra.Structures.d588
                              (coe MAlonzo.Code.Algebra.Structures.d746
                                 (coe MAlonzo.Code.Algebra.Structures.d2050
                                    (coe MAlonzo.Code.Algebra.d1012 v0))))))
                     (coe MAlonzo.Code.Algebra.d1002 v0
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0
                              (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                     (coe MAlonzo.Code.Algebra.d1002 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0
                           (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))))
                  (coe MAlonzo.Code.Algebra.Structures.d126
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.Structures.d746
                              (coe MAlonzo.Code.Algebra.Structures.d2050
                                 (coe MAlonzo.Code.Algebra.d1012 v0)))))
                     (coe MAlonzo.Code.Algebra.d1004 v0
                        (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))))
               (coe du122 v0
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1002 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0
                           (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                           v1)
                        v2)
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                  (coe MAlonzo.Code.Algebra.d1006 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d124
                           (coe MAlonzo.Code.Algebra.Structures.d262
                              (coe MAlonzo.Code.Algebra.Structures.d588
                                 (coe MAlonzo.Code.Algebra.Structures.d746
                                    (coe MAlonzo.Code.Algebra.Structures.d2050
                                       (coe MAlonzo.Code.Algebra.d1012 v0))))))
                        (coe MAlonzo.Code.Algebra.d1004 v0
                           (coe MAlonzo.Code.Algebra.d1002 v0
                              (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                              v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0
                              (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                        (coe MAlonzo.Code.Data.Product.d28
                           (coe MAlonzo.Code.Algebra.Structures.d2054
                              (coe MAlonzo.Code.Algebra.d1012 v0))
                           v2
                           (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                           v1))
                     (coe MAlonzo.Code.Algebra.Structures.d128
                        (coe MAlonzo.Code.Algebra.Structures.d262
                           (coe MAlonzo.Code.Algebra.Structures.d588
                              (coe MAlonzo.Code.Algebra.Structures.d746
                                 (coe MAlonzo.Code.Algebra.Structures.d2050
                                    (coe MAlonzo.Code.Algebra.d1012 v0)))))
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0
                              (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                        (coe MAlonzo.Code.Algebra.d1004 v0
                           (coe MAlonzo.Code.Algebra.d1002 v0
                              (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                              v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe MAlonzo.Code.Algebra.Structures.d124
                           (coe MAlonzo.Code.Algebra.Structures.d262
                              (coe MAlonzo.Code.Algebra.Structures.d588
                                 (coe MAlonzo.Code.Algebra.Structures.d746
                                    (coe MAlonzo.Code.Algebra.Structures.d2050
                                       (coe MAlonzo.Code.Algebra.d1012 v0))))))
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))))
                  (coe du122 v0
                     (coe MAlonzo.Code.Algebra.d1002 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0
                           (coe MAlonzo.Code.Algebra.d1002 v0
                              (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                              v1)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                     (coe MAlonzo.Code.Algebra.d1002 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0
                           (coe MAlonzo.Code.Algebra.d1008 v0)
                           v2)
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Function.du176
                           (coe MAlonzo.Code.Data.Product.d26
                              (coe MAlonzo.Code.Algebra.Structures.d590
                                 (coe MAlonzo.Code.Algebra.Structures.d746
                                    (coe MAlonzo.Code.Algebra.Structures.d2050
                                       (coe MAlonzo.Code.Algebra.d1012 v0))))
                              v1)
                           (coe MAlonzo.Code.Algebra.Structures.d128
                              (coe MAlonzo.Code.Algebra.Structures.d262
                                 (coe MAlonzo.Code.Algebra.Structures.d2052
                                    (coe MAlonzo.Code.Algebra.d1012 v0)))
                              (coe MAlonzo.Code.Algebra.d1002 v0
                                 (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                                 v1)
                              (coe MAlonzo.Code.Algebra.d1008 v0)
                              v2
                              v2)
                           (coe MAlonzo.Code.Relation.Binary.Core.d516
                              (coe MAlonzo.Code.Algebra.Structures.d124
                                 (coe MAlonzo.Code.Algebra.Structures.d262
                                    (coe MAlonzo.Code.Algebra.Structures.d588
                                       (coe MAlonzo.Code.Algebra.Structures.d746
                                          (coe MAlonzo.Code.Algebra.Structures.d2050
                                             (coe MAlonzo.Code.Algebra.d1012 v0))))))
                              v2))
                        (coe MAlonzo.Code.Algebra.Structures.d128
                           (coe MAlonzo.Code.Algebra.Structures.d262
                              (coe MAlonzo.Code.Algebra.Structures.d588
                                 (coe MAlonzo.Code.Algebra.Structures.d746
                                    (coe MAlonzo.Code.Algebra.Structures.d2050
                                       (coe MAlonzo.Code.Algebra.d1012 v0)))))
                           (coe MAlonzo.Code.Algebra.d1004 v0
                              (coe MAlonzo.Code.Algebra.d1002 v0
                                 (coe MAlonzo.Code.Algebra.d1006 v0 v1)
                                 v1)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1004 v0
                              (coe MAlonzo.Code.Algebra.d1008 v0)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe MAlonzo.Code.Algebra.Structures.d124
                              (coe MAlonzo.Code.Algebra.Structures.d262
                                 (coe MAlonzo.Code.Algebra.Structures.d588
                                    (coe MAlonzo.Code.Algebra.Structures.d746
                                       (coe MAlonzo.Code.Algebra.Structures.d2050
                                          (coe MAlonzo.Code.Algebra.d1012 v0))))))
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))))
                     (coe du122 v0
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0
                              (coe MAlonzo.Code.Algebra.d1008 v0)
                              v2)
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1008 v0)
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                        (coe MAlonzo.Code.Function.du176
                           (coe MAlonzo.Code.Data.Product.d26 (coe du114 v0) v2)
                           (coe MAlonzo.Code.Algebra.Structures.d128
                              (coe MAlonzo.Code.Algebra.Structures.d262
                                 (coe MAlonzo.Code.Algebra.Structures.d588
                                    (coe MAlonzo.Code.Algebra.Structures.d746
                                       (coe MAlonzo.Code.Algebra.Structures.d2050
                                          (coe MAlonzo.Code.Algebra.d1012 v0)))))
                              (coe MAlonzo.Code.Algebra.d1004 v0
                                 (coe MAlonzo.Code.Algebra.d1008 v0)
                                 v2)
                              (coe MAlonzo.Code.Algebra.d1008 v0)
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                           (coe MAlonzo.Code.Relation.Binary.Core.d516
                              (coe MAlonzo.Code.Algebra.Structures.d124
                                 (coe MAlonzo.Code.Algebra.Structures.d262
                                    (coe MAlonzo.Code.Algebra.Structures.d588
                                       (coe MAlonzo.Code.Algebra.Structures.d746
                                          (coe MAlonzo.Code.Algebra.Structures.d2050
                                             (coe MAlonzo.Code.Algebra.d1012 v0))))))
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))))
                        (coe du122 v0
                           (coe MAlonzo.Code.Algebra.d1002 v0
                              (coe MAlonzo.Code.Algebra.d1008 v0)
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                           (coe MAlonzo.Code.Data.Product.d26
                              (coe MAlonzo.Code.Algebra.Structures.d264
                                 (coe MAlonzo.Code.Algebra.Structures.d588
                                    (coe MAlonzo.Code.Algebra.Structures.d746
                                       (coe MAlonzo.Code.Algebra.Structures.d2050
                                          (coe MAlonzo.Code.Algebra.d1012 v0)))))
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                           (coe du120 v0
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))))))))))
name166 = "Algebra.Properties.Ring.-\8255*-distrib\691"
d166 v0 v1 v2 v3 v4 = du166 v2 v3 v4
du166 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du122 v0
         (coe MAlonzo.Code.Algebra.d1004 v0 v1
            (coe MAlonzo.Code.Algebra.d1006 v0 v2))
         (coe MAlonzo.Code.Algebra.d1002 v0
            (coe MAlonzo.Code.Algebra.d1008 v0)
            (coe MAlonzo.Code.Algebra.d1004 v0 v1
               (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
         (coe MAlonzo.Code.Algebra.d1006 v0
            (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d124
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.Structures.d746
                           (coe MAlonzo.Code.Algebra.Structures.d2050
                              (coe MAlonzo.Code.Algebra.d1012 v0))))))
               (coe MAlonzo.Code.Algebra.d1002 v0
                  (coe MAlonzo.Code.Algebra.d1008 v0)
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1
                     (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
               (coe MAlonzo.Code.Algebra.d1004 v0 v1
                  (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
            (coe MAlonzo.Code.Data.Product.d26
               (coe MAlonzo.Code.Algebra.Structures.d264
                  (coe MAlonzo.Code.Algebra.Structures.d588
                     (coe MAlonzo.Code.Algebra.Structures.d746
                        (coe MAlonzo.Code.Algebra.Structures.d2050
                           (coe MAlonzo.Code.Algebra.d1012 v0)))))
               (coe MAlonzo.Code.Algebra.d1004 v0 v1
                  (coe MAlonzo.Code.Algebra.d1006 v0 v2))))
         (coe du122 v0
            (coe MAlonzo.Code.Algebra.d1002 v0
               (coe MAlonzo.Code.Algebra.d1008 v0)
               (coe MAlonzo.Code.Algebra.d1004 v0 v1
                  (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
            (coe MAlonzo.Code.Algebra.d1002 v0
               (coe MAlonzo.Code.Algebra.d1002 v0
                  (coe MAlonzo.Code.Algebra.d1006 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.d1004 v0 v1
                  (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
            (coe MAlonzo.Code.Algebra.d1006 v0
               (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.Structures.d746
                              (coe MAlonzo.Code.Algebra.Structures.d2050
                                 (coe MAlonzo.Code.Algebra.d1012 v0))))))
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.d1008 v0)
                  (coe MAlonzo.Code.Data.Product.d26
                     (coe MAlonzo.Code.Algebra.Structures.d590
                        (coe MAlonzo.Code.Algebra.Structures.d746
                           (coe MAlonzo.Code.Algebra.Structures.d2050
                              (coe MAlonzo.Code.Algebra.d1012 v0))))
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
               (coe MAlonzo.Code.Algebra.Structures.d128
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.Structures.d746
                           (coe MAlonzo.Code.Algebra.Structures.d2050
                              (coe MAlonzo.Code.Algebra.d1012 v0)))))
                  (coe MAlonzo.Code.Algebra.d1008 v0)
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1
                     (coe MAlonzo.Code.Algebra.d1006 v0 v2))
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1
                     (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.Structures.d746
                              (coe MAlonzo.Code.Algebra.Structures.d2050
                                 (coe MAlonzo.Code.Algebra.d1012 v0))))))
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1
                     (coe MAlonzo.Code.Algebra.d1006 v0 v2))))
            (coe du122 v0
               (coe MAlonzo.Code.Algebra.d1002 v0
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1
                     (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
               (coe MAlonzo.Code.Algebra.d1002 v0
                  (coe MAlonzo.Code.Algebra.d1006 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1
                        (coe MAlonzo.Code.Algebra.d1006 v0 v2))))
               (coe MAlonzo.Code.Algebra.d1006 v0
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.Structures.d126
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.Structures.d746
                           (coe MAlonzo.Code.Algebra.Structures.d2050
                              (coe MAlonzo.Code.Algebra.d1012 v0)))))
                  (coe MAlonzo.Code.Algebra.d1006 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d1004 v0 v1
                     (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
               (coe du122 v0
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.d1002 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1
                           (coe MAlonzo.Code.Algebra.d1006 v0 v2))))
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1
                        (coe MAlonzo.Code.Algebra.d1002 v0 v2
                           (coe MAlonzo.Code.Algebra.d1006 v0 v2))))
                  (coe MAlonzo.Code.Algebra.d1006 v0
                     (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe MAlonzo.Code.Algebra.Structures.d124
                           (coe MAlonzo.Code.Algebra.Structures.d262
                              (coe MAlonzo.Code.Algebra.Structures.d588
                                 (coe MAlonzo.Code.Algebra.Structures.d746
                                    (coe MAlonzo.Code.Algebra.Structures.d2050
                                       (coe MAlonzo.Code.Algebra.d1012 v0))))))
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                     (coe MAlonzo.Code.Algebra.Structures.d128
                        (coe MAlonzo.Code.Algebra.Structures.d262
                           (coe MAlonzo.Code.Algebra.Structures.d588
                              (coe MAlonzo.Code.Algebra.Structures.d746
                                 (coe MAlonzo.Code.Algebra.Structures.d2050
                                    (coe MAlonzo.Code.Algebra.d1012 v0)))))
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1
                              (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1
                           (coe MAlonzo.Code.Algebra.d1002 v0 v2
                              (coe MAlonzo.Code.Algebra.d1006 v0 v2))))
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d124
                           (coe MAlonzo.Code.Algebra.Structures.d262
                              (coe MAlonzo.Code.Algebra.Structures.d588
                                 (coe MAlonzo.Code.Algebra.Structures.d746
                                    (coe MAlonzo.Code.Algebra.Structures.d2050
                                       (coe MAlonzo.Code.Algebra.d1012 v0))))))
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1
                           (coe MAlonzo.Code.Algebra.d1002 v0 v2
                              (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1
                              (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
                        (coe MAlonzo.Code.Data.Product.d26
                           (coe MAlonzo.Code.Algebra.Structures.d2054
                              (coe MAlonzo.Code.Algebra.d1012 v0))
                           v1
                           v2
                           (coe MAlonzo.Code.Algebra.d1006 v0 v2))))
                  (coe du122 v0
                     (coe MAlonzo.Code.Algebra.d1002 v0
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1
                           (coe MAlonzo.Code.Algebra.d1002 v0 v2
                              (coe MAlonzo.Code.Algebra.d1006 v0 v2))))
                     (coe MAlonzo.Code.Algebra.d1002 v0
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1
                           (coe MAlonzo.Code.Algebra.d1008 v0)))
                     (coe MAlonzo.Code.Algebra.d1006 v0
                        (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe MAlonzo.Code.Algebra.Structures.d124
                              (coe MAlonzo.Code.Algebra.Structures.d262
                                 (coe MAlonzo.Code.Algebra.Structures.d588
                                    (coe MAlonzo.Code.Algebra.Structures.d746
                                       (coe MAlonzo.Code.Algebra.Structures.d2050
                                          (coe MAlonzo.Code.Algebra.d1012 v0))))))
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                        (coe MAlonzo.Code.Algebra.Structures.d128
                           (coe MAlonzo.Code.Algebra.Structures.d262
                              (coe MAlonzo.Code.Algebra.Structures.d588
                                 (coe MAlonzo.Code.Algebra.Structures.d746
                                    (coe MAlonzo.Code.Algebra.Structures.d2050
                                       (coe MAlonzo.Code.Algebra.d1012 v0)))))
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1
                              (coe MAlonzo.Code.Algebra.d1002 v0 v2
                                 (coe MAlonzo.Code.Algebra.d1006 v0 v2)))
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1
                              (coe MAlonzo.Code.Algebra.d1008 v0)))
                        (coe MAlonzo.Code.Function.du176
                           (coe MAlonzo.Code.Relation.Binary.Core.d516
                              (coe MAlonzo.Code.Algebra.Structures.d124
                                 (coe MAlonzo.Code.Algebra.Structures.d262
                                    (coe MAlonzo.Code.Algebra.Structures.d588
                                       (coe MAlonzo.Code.Algebra.Structures.d746
                                          (coe MAlonzo.Code.Algebra.Structures.d2050
                                             (coe MAlonzo.Code.Algebra.d1012 v0))))))
                              v1)
                           (coe MAlonzo.Code.Algebra.Structures.d128
                              (coe MAlonzo.Code.Algebra.Structures.d262
                                 (coe MAlonzo.Code.Algebra.Structures.d2052
                                    (coe MAlonzo.Code.Algebra.d1012 v0)))
                              v1
                              v1
                              (coe MAlonzo.Code.Algebra.d1002 v0 v2
                                 (coe MAlonzo.Code.Algebra.d1006 v0 v2))
                              (coe MAlonzo.Code.Algebra.d1008 v0))
                           (coe MAlonzo.Code.Data.Product.d28
                              (coe MAlonzo.Code.Algebra.Structures.d590
                                 (coe MAlonzo.Code.Algebra.Structures.d746
                                    (coe MAlonzo.Code.Algebra.Structures.d2050
                                       (coe MAlonzo.Code.Algebra.d1012 v0))))
                              v2)))
                     (coe du122 v0
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1
                              (coe MAlonzo.Code.Algebra.d1008 v0)))
                        (coe MAlonzo.Code.Algebra.d1002 v0
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                           (coe MAlonzo.Code.Algebra.d1008 v0))
                        (coe MAlonzo.Code.Algebra.d1006 v0
                           (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                        (coe MAlonzo.Code.Function.du176
                           (coe MAlonzo.Code.Relation.Binary.Core.d516
                              (coe MAlonzo.Code.Algebra.Structures.d124
                                 (coe MAlonzo.Code.Algebra.Structures.d262
                                    (coe MAlonzo.Code.Algebra.Structures.d588
                                       (coe MAlonzo.Code.Algebra.Structures.d746
                                          (coe MAlonzo.Code.Algebra.Structures.d2050
                                             (coe MAlonzo.Code.Algebra.d1012 v0))))))
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                           (coe MAlonzo.Code.Algebra.Structures.d128
                              (coe MAlonzo.Code.Algebra.Structures.d262
                                 (coe MAlonzo.Code.Algebra.Structures.d588
                                    (coe MAlonzo.Code.Algebra.Structures.d746
                                       (coe MAlonzo.Code.Algebra.Structures.d2050
                                          (coe MAlonzo.Code.Algebra.d1012 v0)))))
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1
                                 (coe MAlonzo.Code.Algebra.d1008 v0))
                              (coe MAlonzo.Code.Algebra.d1008 v0))
                           (coe MAlonzo.Code.Data.Product.d28 (coe du114 v0) v1))
                        (coe du122 v0
                           (coe MAlonzo.Code.Algebra.d1002 v0
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                              (coe MAlonzo.Code.Algebra.d1008 v0))
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                           (coe MAlonzo.Code.Algebra.d1006 v0
                              (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))
                           (coe MAlonzo.Code.Data.Product.d28
                              (coe MAlonzo.Code.Algebra.Structures.d264
                                 (coe MAlonzo.Code.Algebra.Structures.d588
                                    (coe MAlonzo.Code.Algebra.Structures.d746
                                       (coe MAlonzo.Code.Algebra.Structures.d2050
                                          (coe MAlonzo.Code.Algebra.d1012 v0)))))
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2)))
                           (coe du120 v0
                              (coe MAlonzo.Code.Algebra.d1006 v0
                                 (coe MAlonzo.Code.Algebra.d1004 v0 v1 v2))))))))))