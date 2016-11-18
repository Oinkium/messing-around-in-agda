{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.Properties.Group where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
name82 = "Algebra.Properties.Group._.Identity"
d82 = erased
name110 = "Algebra.Properties.Group._._\8718"
d110 v0 v1 v2 = du110 v2
du110 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe MAlonzo.Code.Relation.Binary.C85 erased erased
         (coe MAlonzo.Code.Algebra.Structures.d124
            (coe MAlonzo.Code.Algebra.Structures.d262
               (coe MAlonzo.Code.Algebra.Structures.d588
                  (coe MAlonzo.Code.Algebra.d228 v0)))))
name112 = "Algebra.Properties.Group._._\8764\10216_\10217_"
d112 v0 v1 v2 = du112 v2
du112 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40
      (coe MAlonzo.Code.Relation.Binary.C85 erased erased
         (coe MAlonzo.Code.Algebra.Structures.d124
            (coe MAlonzo.Code.Algebra.Structures.d262
               (coe MAlonzo.Code.Algebra.Structures.d588
                  (coe MAlonzo.Code.Algebra.d228 v0)))))
name128 = "Algebra.Properties.Group.\8315\185-involutive"
d128 v0 v1 v2 v3 = du128 v2 v3
du128 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du112 v0
         (coe MAlonzo.Code.Algebra.d226 v0
            (coe MAlonzo.Code.Algebra.d226 v0 v1))
         (coe MAlonzo.Code.Algebra.d222 v0
            (coe MAlonzo.Code.Algebra.d226 v0
               (coe MAlonzo.Code.Algebra.d226 v0 v1))
            (coe MAlonzo.Code.Algebra.d224 v0))
         v1
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d124
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.d228 v0))))
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d226 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1))
                  (coe MAlonzo.Code.Algebra.d224 v0))
               (coe MAlonzo.Code.Algebra.d226 v0
                  (coe MAlonzo.Code.Algebra.d226 v0 v1)))
            (coe MAlonzo.Code.Data.Product.d28
               (coe MAlonzo.Code.Algebra.Structures.d264
                  (coe MAlonzo.Code.Algebra.Structures.d588
                     (coe MAlonzo.Code.Algebra.d228 v0)))
               (coe MAlonzo.Code.Algebra.d226 v0
                  (coe MAlonzo.Code.Algebra.d226 v0 v1))))
         (coe du112 v0
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d226 v0
                  (coe MAlonzo.Code.Algebra.d226 v0 v1))
               (coe MAlonzo.Code.Algebra.d224 v0))
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d226 v0
                  (coe MAlonzo.Code.Algebra.d226 v0 v1))
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d226 v0 v1)
                  v1))
            v1
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  (coe MAlonzo.Code.Algebra.d226 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1)))
               (coe MAlonzo.Code.Algebra.Structures.d128
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.d228 v0)))
                  (coe MAlonzo.Code.Algebra.d226 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1))
                  (coe MAlonzo.Code.Algebra.d226 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1))
                  (coe MAlonzo.Code.Algebra.d224 v0)
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1)
                     v1))
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1)
                     v1)
                  (coe MAlonzo.Code.Algebra.d224 v0)
                  (coe MAlonzo.Code.Data.Product.d26
                     (coe MAlonzo.Code.Algebra.Structures.d590
                        (coe MAlonzo.Code.Algebra.d228 v0))
                     v1)))
            (coe du112 v0
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d226 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1))
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1)
                     v1))
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d226 v0
                        (coe MAlonzo.Code.Algebra.d226 v0 v1))
                     (coe MAlonzo.Code.Algebra.d226 v0 v1))
                  v1)
               v1
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe MAlonzo.Code.Algebra.Structures.d124
                        (coe MAlonzo.Code.Algebra.Structures.d262
                           (coe MAlonzo.Code.Algebra.Structures.d588
                              (coe MAlonzo.Code.Algebra.d228 v0))))
                     (coe MAlonzo.Code.Algebra.d222 v0
                        (coe MAlonzo.Code.Algebra.d222 v0
                           (coe MAlonzo.Code.Algebra.d226 v0
                              (coe MAlonzo.Code.Algebra.d226 v0 v1))
                           (coe MAlonzo.Code.Algebra.d226 v0 v1))
                        v1)
                     (coe MAlonzo.Code.Algebra.d222 v0
                        (coe MAlonzo.Code.Algebra.d226 v0
                           (coe MAlonzo.Code.Algebra.d226 v0 v1))
                        (coe MAlonzo.Code.Algebra.d222 v0
                           (coe MAlonzo.Code.Algebra.d226 v0 v1)
                           v1)))
                  (coe MAlonzo.Code.Algebra.Structures.d126
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0)))
                     (coe MAlonzo.Code.Algebra.d226 v0
                        (coe MAlonzo.Code.Algebra.d226 v0 v1))
                     (coe MAlonzo.Code.Algebra.d226 v0 v1)
                     v1))
               (coe du112 v0
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d222 v0
                        (coe MAlonzo.Code.Algebra.d226 v0
                           (coe MAlonzo.Code.Algebra.d226 v0 v1))
                        (coe MAlonzo.Code.Algebra.d226 v0 v1))
                     v1)
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d224 v0)
                     v1)
                  v1
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Data.Product.d26
                        (coe MAlonzo.Code.Algebra.Structures.d590
                           (coe MAlonzo.Code.Algebra.d228 v0))
                        (coe MAlonzo.Code.Algebra.d226 v0 v1))
                     (coe MAlonzo.Code.Algebra.Structures.d128
                        (coe MAlonzo.Code.Algebra.Structures.d262
                           (coe MAlonzo.Code.Algebra.Structures.d588
                              (coe MAlonzo.Code.Algebra.d228 v0)))
                        (coe MAlonzo.Code.Algebra.d222 v0
                           (coe MAlonzo.Code.Algebra.d226 v0
                              (coe MAlonzo.Code.Algebra.d226 v0 v1))
                           (coe MAlonzo.Code.Algebra.d226 v0 v1))
                        (coe MAlonzo.Code.Algebra.d224 v0)
                        v1
                        v1)
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe MAlonzo.Code.Algebra.Structures.d124
                           (coe MAlonzo.Code.Algebra.Structures.d262
                              (coe MAlonzo.Code.Algebra.Structures.d588
                                 (coe MAlonzo.Code.Algebra.d228 v0))))
                        v1))
                  (coe du112 v0
                     (coe MAlonzo.Code.Algebra.d222 v0
                        (coe MAlonzo.Code.Algebra.d224 v0)
                        v1)
                     v1
                     v1
                     (coe MAlonzo.Code.Data.Product.d26
                        (coe MAlonzo.Code.Algebra.Structures.d264
                           (coe MAlonzo.Code.Algebra.Structures.d588
                              (coe MAlonzo.Code.Algebra.d228 v0)))
                        v1)
                     (coe du110 v0 v1))))))
name136 = "Algebra.Properties.Group.left-helper"
d136 v0 v1 v2 v3 v4 = du136 v2 v3 v4
du136 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du112 v0 v1
         (coe MAlonzo.Code.Algebra.d222 v0 v1
            (coe MAlonzo.Code.Algebra.d224 v0))
         (coe MAlonzo.Code.Algebra.d222 v0
            (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d226 v0 v2))
         (coe MAlonzo.Code.Relation.Binary.Core.d518
            (coe MAlonzo.Code.Algebra.Structures.d124
               (coe MAlonzo.Code.Algebra.Structures.d262
                  (coe MAlonzo.Code.Algebra.Structures.d588
                     (coe MAlonzo.Code.Algebra.d228 v0))))
            (coe MAlonzo.Code.Algebra.d222 v0 v1
               (coe MAlonzo.Code.Algebra.d224 v0))
            v1
            (coe MAlonzo.Code.Data.Product.d28
               (coe MAlonzo.Code.Algebra.Structures.d264
                  (coe MAlonzo.Code.Algebra.Structures.d588
                     (coe MAlonzo.Code.Algebra.d228 v0)))
               v1))
         (coe du112 v0
            (coe MAlonzo.Code.Algebra.d222 v0 v1
               (coe MAlonzo.Code.Algebra.d224 v0))
            (coe MAlonzo.Code.Algebra.d222 v0 v1
               (coe MAlonzo.Code.Algebra.d222 v0 v2
                  (coe MAlonzo.Code.Algebra.d226 v0 v2)))
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d226 v0 v2))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  v1)
               (coe MAlonzo.Code.Algebra.Structures.d128
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.d228 v0)))
                  v1
                  v1
                  (coe MAlonzo.Code.Algebra.d224 v0)
                  (coe MAlonzo.Code.Algebra.d222 v0 v2
                     (coe MAlonzo.Code.Algebra.d226 v0 v2)))
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  (coe MAlonzo.Code.Algebra.d222 v0 v2
                     (coe MAlonzo.Code.Algebra.d226 v0 v2))
                  (coe MAlonzo.Code.Algebra.d224 v0)
                  (coe MAlonzo.Code.Data.Product.d28
                     (coe MAlonzo.Code.Algebra.Structures.d590
                        (coe MAlonzo.Code.Algebra.d228 v0))
                     v2)))
            (coe du112 v0
               (coe MAlonzo.Code.Algebra.d222 v0 v1
                  (coe MAlonzo.Code.Algebra.d222 v0 v2
                     (coe MAlonzo.Code.Algebra.d226 v0 v2)))
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d226 v0 v2))
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d226 v0 v2))
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d226 v0 v2))
                  (coe MAlonzo.Code.Algebra.d222 v0 v1
                     (coe MAlonzo.Code.Algebra.d222 v0 v2
                        (coe MAlonzo.Code.Algebra.d226 v0 v2)))
                  (coe MAlonzo.Code.Algebra.Structures.d126
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0)))
                     v1
                     v2
                     (coe MAlonzo.Code.Algebra.d226 v0 v2)))
               (coe du110 v0
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.d226 v0 v2))))))
name146 = "Algebra.Properties.Group.right-helper"
d146 v0 v1 v2 v3 v4 = du146 v2 v3 v4
du146 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du112 v0 v2
         (coe MAlonzo.Code.Algebra.d222 v0
            (coe MAlonzo.Code.Algebra.d224 v0)
            v2)
         (coe MAlonzo.Code.Algebra.d222 v0
            (coe MAlonzo.Code.Algebra.d226 v0 v1)
            (coe MAlonzo.Code.Algebra.d222 v0 v1 v2))
         (coe MAlonzo.Code.Relation.Binary.Core.d518
            (coe MAlonzo.Code.Algebra.Structures.d124
               (coe MAlonzo.Code.Algebra.Structures.d262
                  (coe MAlonzo.Code.Algebra.Structures.d588
                     (coe MAlonzo.Code.Algebra.d228 v0))))
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d224 v0)
               v2)
            v2
            (coe MAlonzo.Code.Data.Product.d26
               (coe MAlonzo.Code.Algebra.Structures.d264
                  (coe MAlonzo.Code.Algebra.Structures.d588
                     (coe MAlonzo.Code.Algebra.d228 v0)))
               v2))
         (coe du112 v0
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d224 v0)
               v2)
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d226 v0 v1)
                  v1)
               v2)
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d226 v0 v1)
               (coe MAlonzo.Code.Algebra.d222 v0 v1 v2))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1)
                     v1)
                  (coe MAlonzo.Code.Algebra.d224 v0)
                  (coe MAlonzo.Code.Data.Product.d26
                     (coe MAlonzo.Code.Algebra.Structures.d590
                        (coe MAlonzo.Code.Algebra.d228 v0))
                     v1))
               (coe MAlonzo.Code.Algebra.Structures.d128
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.d228 v0)))
                  (coe MAlonzo.Code.Algebra.d224 v0)
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1)
                     v1)
                  v2
                  v2)
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  v2))
            (coe du112 v0
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1)
                     v1)
                  v2)
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d226 v0 v1)
                  (coe MAlonzo.Code.Algebra.d222 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d226 v0 v1)
                  (coe MAlonzo.Code.Algebra.d222 v0 v1 v2))
               (coe MAlonzo.Code.Algebra.Structures.d126
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.d228 v0)))
                  (coe MAlonzo.Code.Algebra.d226 v0 v1)
                  v1
                  v2)
               (coe du110 v0
                  (coe MAlonzo.Code.Algebra.d222 v0
                     (coe MAlonzo.Code.Algebra.d226 v0 v1)
                     (coe MAlonzo.Code.Algebra.d222 v0 v1 v2))))))
name156 = "Algebra.Properties.Group.left-identity-unique"
d156 v0 v1 v2 v3 v4 v5 = du156 v2 v3 v4 v5
du156 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du112 v0 v1
         (coe MAlonzo.Code.Algebra.d222 v0
            (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d226 v0 v2))
         (coe MAlonzo.Code.Algebra.d224 v0)
         (coe du136 v0 v1 v2)
         (coe du112 v0
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d226 v0 v2))
            (coe MAlonzo.Code.Algebra.d222 v0 v2
               (coe MAlonzo.Code.Algebra.d226 v0 v2))
            (coe MAlonzo.Code.Algebra.d224 v0)
            (coe MAlonzo.Code.Function.du176 v3
               (coe MAlonzo.Code.Algebra.Structures.d128
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.d228 v0)))
                  (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
                  v2
                  (coe MAlonzo.Code.Algebra.d226 v0 v2)
                  (coe MAlonzo.Code.Algebra.d226 v0 v2))
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  (coe MAlonzo.Code.Algebra.d226 v0 v2)))
            (coe du112 v0
               (coe MAlonzo.Code.Algebra.d222 v0 v2
                  (coe MAlonzo.Code.Algebra.d226 v0 v2))
               (coe MAlonzo.Code.Algebra.d224 v0)
               (coe MAlonzo.Code.Algebra.d224 v0)
               (coe MAlonzo.Code.Data.Product.d28
                  (coe MAlonzo.Code.Algebra.Structures.d590
                     (coe MAlonzo.Code.Algebra.d228 v0))
                  v2)
               (coe du110 v0 (coe MAlonzo.Code.Algebra.d224 v0)))))
name168 = "Algebra.Properties.Group.right-identity-unique"
d168 v0 v1 v2 v3 v4 v5 = du168 v2 v3 v4 v5
du168 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du112 v0 v2
         (coe MAlonzo.Code.Algebra.d222 v0
            (coe MAlonzo.Code.Algebra.d226 v0 v1)
            (coe MAlonzo.Code.Algebra.d222 v0 v1 v2))
         (coe MAlonzo.Code.Algebra.d224 v0)
         (coe du146 v0 v1 v2)
         (coe du112 v0
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d226 v0 v1)
               (coe MAlonzo.Code.Algebra.d222 v0 v1 v2))
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d226 v0 v1)
               v1)
            (coe MAlonzo.Code.Algebra.d224 v0)
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  (coe MAlonzo.Code.Algebra.d226 v0 v1))
               (coe MAlonzo.Code.Algebra.Structures.d128
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.d228 v0)))
                  (coe MAlonzo.Code.Algebra.d226 v0 v1)
                  (coe MAlonzo.Code.Algebra.d226 v0 v1)
                  (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
                  v1)
               v3)
            (coe du112 v0
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d226 v0 v1)
                  v1)
               (coe MAlonzo.Code.Algebra.d224 v0)
               (coe MAlonzo.Code.Algebra.d224 v0)
               (coe MAlonzo.Code.Data.Product.d26
                  (coe MAlonzo.Code.Algebra.Structures.d590
                     (coe MAlonzo.Code.Algebra.d228 v0))
                  v1)
               (coe du110 v0 (coe MAlonzo.Code.Algebra.d224 v0)))))
name178 = "Algebra.Properties.Group.identity-unique"
d178 v0 v1 v2 v3 v4 = du178 v2 v3 v4
du178 v0 v1 v2
  = coe du156 v0 v1 v1 (coe MAlonzo.Code.Data.Product.d28 v2 v1)
name188 = "Algebra.Properties.Group.left-inverse-unique"
d188 v0 v1 v2 v3 v4 v5 = du188 v2 v3 v4 v5
du188 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du112 v0 v1
         (coe MAlonzo.Code.Algebra.d222 v0
            (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.d226 v0 v2))
         (coe MAlonzo.Code.Algebra.d226 v0 v2)
         (coe du136 v0 v1 v2)
         (coe du112 v0
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.d226 v0 v2))
            (coe MAlonzo.Code.Algebra.d222 v0
               (coe MAlonzo.Code.Algebra.d224 v0)
               (coe MAlonzo.Code.Algebra.d226 v0 v2))
            (coe MAlonzo.Code.Algebra.d226 v0 v2)
            (coe MAlonzo.Code.Function.du176 v3
               (coe MAlonzo.Code.Algebra.Structures.d128
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.d228 v0)))
                  (coe MAlonzo.Code.Algebra.d222 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.d224 v0)
                  (coe MAlonzo.Code.Algebra.d226 v0 v2)
                  (coe MAlonzo.Code.Algebra.d226 v0 v2))
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  (coe MAlonzo.Code.Algebra.d226 v0 v2)))
            (coe du112 v0
               (coe MAlonzo.Code.Algebra.d222 v0
                  (coe MAlonzo.Code.Algebra.d224 v0)
                  (coe MAlonzo.Code.Algebra.d226 v0 v2))
               (coe MAlonzo.Code.Algebra.d226 v0 v2)
               (coe MAlonzo.Code.Algebra.d226 v0 v2)
               (coe MAlonzo.Code.Data.Product.d26
                  (coe MAlonzo.Code.Algebra.Structures.d264
                     (coe MAlonzo.Code.Algebra.Structures.d588
                        (coe MAlonzo.Code.Algebra.d228 v0)))
                  (coe MAlonzo.Code.Algebra.d226 v0 v2))
               (coe du110 v0 (coe MAlonzo.Code.Algebra.d226 v0 v2)))))
name200 = "Algebra.Properties.Group.right-inverse-unique"
d200 v0 v1 v2 v3 v4 v5 = du200 v2 v3 v4 v5
du200 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du112 v0 v2
         (coe MAlonzo.Code.Algebra.d226 v0
            (coe MAlonzo.Code.Algebra.d226 v0 v2))
         (coe MAlonzo.Code.Algebra.d226 v0 v1)
         (coe MAlonzo.Code.Relation.Binary.Core.d518
            (coe MAlonzo.Code.Algebra.Structures.d124
               (coe MAlonzo.Code.Algebra.Structures.d262
                  (coe MAlonzo.Code.Algebra.Structures.d588
                     (coe MAlonzo.Code.Algebra.d228 v0))))
            (coe MAlonzo.Code.Algebra.d226 v0
               (coe MAlonzo.Code.Algebra.d226 v0 v2))
            v2
            (coe du128 v0 v2))
         (coe du112 v0
            (coe MAlonzo.Code.Algebra.d226 v0
               (coe MAlonzo.Code.Algebra.d226 v0 v2))
            (coe MAlonzo.Code.Algebra.d226 v0 v1)
            (coe MAlonzo.Code.Algebra.d226 v0 v1)
            (coe MAlonzo.Code.Algebra.Structures.d592
               (coe MAlonzo.Code.Algebra.d228 v0)
               (coe MAlonzo.Code.Algebra.d226 v0 v2)
               v1
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe MAlonzo.Code.Algebra.Structures.d124
                     (coe MAlonzo.Code.Algebra.Structures.d262
                        (coe MAlonzo.Code.Algebra.Structures.d588
                           (coe MAlonzo.Code.Algebra.d228 v0))))
                  v1
                  (coe MAlonzo.Code.Algebra.d226 v0 v2)
                  (coe du188 v0 v1 v2 v3)))
            (coe du110 v0 (coe MAlonzo.Code.Algebra.d226 v0 v1))))