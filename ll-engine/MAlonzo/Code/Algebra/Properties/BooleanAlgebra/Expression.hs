{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.Properties.BooleanAlgebra.Expression
       where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Category.Applicative
import qualified MAlonzo.Code.Category.Applicative.Indexed
import qualified MAlonzo.Code.Category.Monad
import qualified MAlonzo.Code.Category.Monad.Identity
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Vec
import qualified MAlonzo.Code.Data.Vec.Properties
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified MAlonzo.Code.Relation.Binary.Reflection
import qualified MAlonzo.Code.Relation.Binary.Vec.Pointwise
name38 = "Algebra.Properties.BooleanAlgebra.Expression._.reflexive"
d38 v0 v1 = du38 v1
du38 v0 = coe MAlonzo.Code.Algebra.du1436 v0
name74 = "Algebra.Properties.BooleanAlgebra.Expression.Expr"
d74 a0 a1 a2 = ()

data T74 a0 a1 = C80 a0
               | C86 a0 a1
               | C92 a0 a1
               | C96 a0
               | C98
               | C100
name130
  = "Algebra.Properties.BooleanAlgebra.Expression.Semantics.\10214_\10215"
d130 v0 v1 v2 v3 v4 v5 v6 = du130 v1 v3 v5 v6
du130 v0 v1 v2 v3
  = case coe v2 of
        C80 v4 -> coe MAlonzo.Code.Data.Vec.du696 v4 v3
        C86 v4 v5 -> coe MAlonzo.Code.Category.Applicative.Indexed.d68 v1
                       erased
                       erased
                       erased
                       erased
                       erased
                       (coe MAlonzo.Code.Category.Applicative.Indexed.d68 v1 erased erased
                          erased
                          erased
                          ()
                          (coe MAlonzo.Code.Category.Applicative.Indexed.d56 v1 erased ()
                             (coe MAlonzo.Code.Algebra.d1412 v0))
                          (coe du130 v0 v1 v4 v3))
                       (coe du130 v0 v1 v5 v3)
        C92 v4 v5 -> coe MAlonzo.Code.Category.Applicative.Indexed.d68 v1
                       erased
                       erased
                       erased
                       erased
                       erased
                       (coe MAlonzo.Code.Category.Applicative.Indexed.d68 v1 erased erased
                          erased
                          erased
                          ()
                          (coe MAlonzo.Code.Category.Applicative.Indexed.d56 v1 erased ()
                             (coe MAlonzo.Code.Algebra.d1414 v0))
                          (coe du130 v0 v1 v4 v3))
                       (coe du130 v0 v1 v5 v3)
        C96 v4 -> coe MAlonzo.Code.Category.Applicative.Indexed.d68 v1
                    erased
                    erased
                    erased
                    erased
                    erased
                    (coe MAlonzo.Code.Category.Applicative.Indexed.d56 v1 erased ()
                       (coe MAlonzo.Code.Algebra.d1416 v0))
                    (coe du130 v0 v1 v4 v3)
        C98 -> coe MAlonzo.Code.Category.Applicative.Indexed.d56 v1 erased
                 erased
                 (coe MAlonzo.Code.Algebra.d1418 v0)
        C100 -> coe MAlonzo.Code.Category.Applicative.Indexed.d56 v1 erased
                  erased
                  (coe MAlonzo.Code.Algebra.d1420 v0)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name220
  = "Algebra.Properties.BooleanAlgebra.Expression.Naturality._.\10214_\10215"
d220 v0 v1 v2 v3 v4 v5 v6 = du220 v1 v4
du220 v0 v1 = coe d130 erased v0 erased v1
name224
  = "Algebra.Properties.BooleanAlgebra.Expression.Naturality._.\10214_\10215"
d224 v0 v1 v2 v3 v4 v5 v6 = du224 v1 v5
du224 v0 v1 = coe d130 erased v0 erased v1
name238
  = "Algebra.Properties.BooleanAlgebra.Expression.Naturality._._\8859_"
d238 v0 v1 v2 v3 v4 v5 v6 = du238 v4
du238 v0 = coe MAlonzo.Code.Category.Applicative.Indexed.d68 v0
name240
  = "Algebra.Properties.BooleanAlgebra.Expression.Naturality._.pure"
d240 v0 v1 v2 v3 v4 v5 v6 = du240 v4
du240 v0 = coe MAlonzo.Code.Category.Applicative.Indexed.d56 v0
name258
  = "Algebra.Properties.BooleanAlgebra.Expression.Naturality._._\8859_"
d258 v0 v1 v2 v3 v4 v5 v6 = du258 v5
du258 v0 = coe MAlonzo.Code.Category.Applicative.Indexed.d68 v0
name260
  = "Algebra.Properties.BooleanAlgebra.Expression.Naturality._.pure"
d260 v0 v1 v2 v3 v4 v5 v6 = du260 v5
du260 v0 = coe MAlonzo.Code.Category.Applicative.Indexed.d56 v0
name270
  = "Algebra.Properties.BooleanAlgebra.Expression.Naturality.natural"
d270 = erased
name296 = "Algebra.Properties.BooleanAlgebra.Expression.lift"
d296 v0 v1 v2 = du296 v1 v2
du296 v0 v1
  = coe MAlonzo.Code.Algebra.C375 erased erased
      (coe MAlonzo.Code.Data.Vec.d212 erased erased erased v1 erased
         erased
         erased
         (coe MAlonzo.Code.Algebra.d1412 v0))
      (coe MAlonzo.Code.Data.Vec.d212 erased erased erased v1 erased
         erased
         erased
         (coe MAlonzo.Code.Algebra.d1414 v0))
      (coe MAlonzo.Code.Data.Vec.d192 erased erased v1 erased erased
         (coe MAlonzo.Code.Algebra.d1416 v0))
      (coe MAlonzo.Code.Data.Vec.du166 v1
         (coe MAlonzo.Code.Algebra.d1418 v0))
      (coe MAlonzo.Code.Data.Vec.du166 v1
         (coe MAlonzo.Code.Algebra.d1420 v0))
      (coe MAlonzo.Code.Algebra.Structures.C605
         (coe MAlonzo.Code.Algebra.Structures.C573
            (coe MAlonzo.Code.Algebra.Structures.C539
               (coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.du300
                  (coe MAlonzo.Code.Algebra.Structures.d2482
                     (coe MAlonzo.Code.Algebra.Structures.d2630
                        (coe MAlonzo.Code.Algebra.Structures.d2798
                           (coe MAlonzo.Code.Algebra.d1422 v0)))))
               (\ v2 v3 ->
                  coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
                    (\ v4 ->
                       coe du338 v0 v1 v4 (2 :: Integer)
                         (\ v5 v6 ->
                            coe MAlonzo.Code.Data.Product.C30 (coe C86 v5 v6) (coe C86 v6 v5))
                         (\ v5 v6 ->
                            coe MAlonzo.Code.Algebra.Structures.d2484
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0)))
                              (coe du130 v0
                                 (coe MAlonzo.Code.Category.Monad.du72
                                    MAlonzo.Code.Category.Monad.Identity.du14)
                                 (coe C80
                                    (coe MAlonzo.Code.Function.du68
                                       (coe MAlonzo.Code.Data.Fin.C8 (1 :: Integer))))
                                 (coe MAlonzo.Code.Data.Vec.du192 (2 :: Integer)
                                    (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v4)
                                    (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v5
                                       (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v6
                                          (coe MAlonzo.Code.Data.Vec.C14)))))
                              (coe du130 v0
                                 (coe MAlonzo.Code.Category.Monad.du72
                                    MAlonzo.Code.Category.Monad.Identity.du14)
                                 (coe C80
                                    (coe MAlonzo.Code.Function.du38
                                       (\ v7 -> coe MAlonzo.Code.Function.d68 erased erased)
                                       (coe MAlonzo.Code.Data.Fin.C14 (1 :: Integer))
                                       (coe MAlonzo.Code.Data.Fin.C8 (0 :: Integer))))
                                 (coe MAlonzo.Code.Data.Vec.du192 (2 :: Integer)
                                    (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v4)
                                    (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v5
                                       (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v6
                                          (coe MAlonzo.Code.Data.Vec.C14))))))
                         v2
                         v3))
               (\ v2 v3 v4 ->
                  coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
                    (\ v5 ->
                       coe du338 v0 v1 v5 (3 :: Integer)
                         (\ v6 v7 v8 ->
                            coe MAlonzo.Code.Data.Product.C30 (coe C86 (coe C86 v6 v7) v8)
                              (coe C86 v6 (coe C86 v7 v8)))
                         (\ v6 v7 v8 ->
                            coe MAlonzo.Code.Algebra.Structures.d2486
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0)))
                              (coe du130 v0
                                 (coe MAlonzo.Code.Category.Monad.du72
                                    MAlonzo.Code.Category.Monad.Identity.du14)
                                 (coe C80
                                    (coe MAlonzo.Code.Function.du68
                                       (coe MAlonzo.Code.Data.Fin.C8 (2 :: Integer))))
                                 (coe MAlonzo.Code.Data.Vec.du192 (3 :: Integer)
                                    (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v5)
                                    (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) v6
                                       (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v7
                                          (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v8
                                             (coe MAlonzo.Code.Data.Vec.C14))))))
                              (coe du130 v0
                                 (coe MAlonzo.Code.Category.Monad.du72
                                    MAlonzo.Code.Category.Monad.Identity.du14)
                                 (coe C80
                                    (coe MAlonzo.Code.Function.du38
                                       (\ v9 -> coe MAlonzo.Code.Function.d68 erased erased)
                                       (coe MAlonzo.Code.Data.Fin.C14 (2 :: Integer))
                                       (coe MAlonzo.Code.Data.Fin.C8 (1 :: Integer))))
                                 (coe MAlonzo.Code.Data.Vec.du192 (3 :: Integer)
                                    (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v5)
                                    (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) v6
                                       (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v7
                                          (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v8
                                             (coe MAlonzo.Code.Data.Vec.C14))))))
                              (coe du130 v0
                                 (coe MAlonzo.Code.Category.Monad.du72
                                    MAlonzo.Code.Category.Monad.Identity.du14)
                                 (coe C80
                                    (coe MAlonzo.Code.Function.du38
                                       (\ v9 ->
                                          coe MAlonzo.Code.Function.d38 erased erased erased erased
                                            erased
                                            erased
                                            (\ v10 -> coe MAlonzo.Code.Function.d68 erased erased)
                                            (coe MAlonzo.Code.Data.Fin.C14 (2 :: Integer)))
                                       (coe MAlonzo.Code.Data.Fin.C14 (1 :: Integer))
                                       (coe MAlonzo.Code.Data.Fin.C8 (0 :: Integer))))
                                 (coe MAlonzo.Code.Data.Vec.du192 (3 :: Integer)
                                    (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v5)
                                    (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) v6
                                       (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v7
                                          (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v8
                                             (coe MAlonzo.Code.Data.Vec.C14)))))))
                         v2
                         v3
                         v4))
               (\ v2 v3 v4 v5 v6 v7 ->
                  coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
                    (\ v8 ->
                       coe du340 v0 v1 v8 (4 :: Integer)
                         (\ v9 v10 v11 v12 ->
                            coe MAlonzo.Code.Data.Product.C30 (coe C86 v9 v10)
                              (coe C86 v11 v12))
                         v2
                         v4
                         v3
                         v5
                         (coe MAlonzo.Code.Algebra.Structures.d2488
                            (coe MAlonzo.Code.Algebra.Structures.d2630
                               (coe MAlonzo.Code.Algebra.Structures.d2798
                                  (coe MAlonzo.Code.Algebra.d1422 v0)))
                            (coe MAlonzo.Code.Data.Vec.du696 v8 v2)
                            (coe MAlonzo.Code.Data.Vec.du696 v8 v3)
                            (coe MAlonzo.Code.Data.Vec.du696 v8 v4)
                            (coe MAlonzo.Code.Data.Vec.du696 v8 v5)
                            (coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.d44 v6 v8)
                            (coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.d44 v7 v8))))
               (\ v2 v3 ->
                  coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
                    (\ v4 ->
                       coe du338 v0 v1 v4 (2 :: Integer)
                         (\ v5 v6 ->
                            coe MAlonzo.Code.Data.Product.C30 (coe C92 v5 v6) (coe C92 v6 v5))
                         (\ v5 v6 ->
                            coe MAlonzo.Code.Algebra.Structures.d2490
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0)))
                              (coe du130 v0
                                 (coe MAlonzo.Code.Category.Monad.du72
                                    MAlonzo.Code.Category.Monad.Identity.du14)
                                 (coe C80
                                    (coe MAlonzo.Code.Function.du68
                                       (coe MAlonzo.Code.Data.Fin.C8 (1 :: Integer))))
                                 (coe MAlonzo.Code.Data.Vec.du192 (2 :: Integer)
                                    (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v4)
                                    (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v5
                                       (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v6
                                          (coe MAlonzo.Code.Data.Vec.C14)))))
                              (coe du130 v0
                                 (coe MAlonzo.Code.Category.Monad.du72
                                    MAlonzo.Code.Category.Monad.Identity.du14)
                                 (coe C80
                                    (coe MAlonzo.Code.Function.du38
                                       (\ v7 -> coe MAlonzo.Code.Function.d68 erased erased)
                                       (coe MAlonzo.Code.Data.Fin.C14 (1 :: Integer))
                                       (coe MAlonzo.Code.Data.Fin.C8 (0 :: Integer))))
                                 (coe MAlonzo.Code.Data.Vec.du192 (2 :: Integer)
                                    (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v4)
                                    (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v5
                                       (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v6
                                          (coe MAlonzo.Code.Data.Vec.C14))))))
                         v2
                         v3))
               (\ v2 v3 v4 ->
                  coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
                    (\ v5 ->
                       coe du338 v0 v1 v5 (3 :: Integer)
                         (\ v6 v7 v8 ->
                            coe MAlonzo.Code.Data.Product.C30 (coe C92 (coe C92 v6 v7) v8)
                              (coe C92 v6 (coe C92 v7 v8)))
                         (\ v6 v7 v8 ->
                            coe MAlonzo.Code.Algebra.Structures.d2492
                              (coe MAlonzo.Code.Algebra.Structures.d2630
                                 (coe MAlonzo.Code.Algebra.Structures.d2798
                                    (coe MAlonzo.Code.Algebra.d1422 v0)))
                              (coe du130 v0
                                 (coe MAlonzo.Code.Category.Monad.du72
                                    MAlonzo.Code.Category.Monad.Identity.du14)
                                 (coe C80
                                    (coe MAlonzo.Code.Function.du68
                                       (coe MAlonzo.Code.Data.Fin.C8 (2 :: Integer))))
                                 (coe MAlonzo.Code.Data.Vec.du192 (3 :: Integer)
                                    (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v5)
                                    (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) v6
                                       (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v7
                                          (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v8
                                             (coe MAlonzo.Code.Data.Vec.C14))))))
                              (coe du130 v0
                                 (coe MAlonzo.Code.Category.Monad.du72
                                    MAlonzo.Code.Category.Monad.Identity.du14)
                                 (coe C80
                                    (coe MAlonzo.Code.Function.du38
                                       (\ v9 -> coe MAlonzo.Code.Function.d68 erased erased)
                                       (coe MAlonzo.Code.Data.Fin.C14 (2 :: Integer))
                                       (coe MAlonzo.Code.Data.Fin.C8 (1 :: Integer))))
                                 (coe MAlonzo.Code.Data.Vec.du192 (3 :: Integer)
                                    (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v5)
                                    (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) v6
                                       (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v7
                                          (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v8
                                             (coe MAlonzo.Code.Data.Vec.C14))))))
                              (coe du130 v0
                                 (coe MAlonzo.Code.Category.Monad.du72
                                    MAlonzo.Code.Category.Monad.Identity.du14)
                                 (coe C80
                                    (coe MAlonzo.Code.Function.du38
                                       (\ v9 ->
                                          coe MAlonzo.Code.Function.d38 erased erased erased erased
                                            erased
                                            erased
                                            (\ v10 -> coe MAlonzo.Code.Function.d68 erased erased)
                                            (coe MAlonzo.Code.Data.Fin.C14 (2 :: Integer)))
                                       (coe MAlonzo.Code.Data.Fin.C14 (1 :: Integer))
                                       (coe MAlonzo.Code.Data.Fin.C8 (0 :: Integer))))
                                 (coe MAlonzo.Code.Data.Vec.du192 (3 :: Integer)
                                    (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v5)
                                    (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) v6
                                       (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v7
                                          (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v8
                                             (coe MAlonzo.Code.Data.Vec.C14)))))))
                         v2
                         v3
                         v4))
               (\ v2 v3 v4 v5 v6 v7 ->
                  coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
                    (\ v8 ->
                       coe du340 v0 v1 v8 (4 :: Integer)
                         (\ v9 v10 v11 v12 ->
                            coe MAlonzo.Code.Data.Product.C30 (coe C92 v9 v10)
                              (coe C92 v11 v12))
                         v2
                         v4
                         v3
                         v5
                         (coe MAlonzo.Code.Algebra.Structures.d2494
                            (coe MAlonzo.Code.Algebra.Structures.d2630
                               (coe MAlonzo.Code.Algebra.Structures.d2798
                                  (coe MAlonzo.Code.Algebra.d1422 v0)))
                            (coe MAlonzo.Code.Data.Vec.du696 v8 v2)
                            (coe MAlonzo.Code.Data.Vec.du696 v8 v3)
                            (coe MAlonzo.Code.Data.Vec.du696 v8 v4)
                            (coe MAlonzo.Code.Data.Vec.du696 v8 v5)
                            (coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.d44 v6 v8)
                            (coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.d44 v7 v8))))
               (coe MAlonzo.Code.Data.Product.C30
                  (\ v2 v3 ->
                     coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
                       (\ v4 ->
                          coe du338 v0 v1 v4 (2 :: Integer)
                            (\ v5 v6 ->
                               coe MAlonzo.Code.Data.Product.C30 (coe C86 v5 (coe C92 v5 v6)) v5)
                            (\ v5 v6 ->
                               coe MAlonzo.Code.Data.Product.d26
                                 (coe MAlonzo.Code.Algebra.Structures.d2496
                                    (coe MAlonzo.Code.Algebra.Structures.d2630
                                       (coe MAlonzo.Code.Algebra.Structures.d2798
                                          (coe MAlonzo.Code.Algebra.d1422 v0))))
                                 (coe du130 v0
                                    (coe MAlonzo.Code.Category.Monad.du72
                                       MAlonzo.Code.Category.Monad.Identity.du14)
                                    (coe C80
                                       (coe MAlonzo.Code.Function.du68
                                          (coe MAlonzo.Code.Data.Fin.C8 (1 :: Integer))))
                                    (coe MAlonzo.Code.Data.Vec.du192 (2 :: Integer)
                                       (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v4)
                                       (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v5
                                          (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v6
                                             (coe MAlonzo.Code.Data.Vec.C14)))))
                                 (coe du130 v0
                                    (coe MAlonzo.Code.Category.Monad.du72
                                       MAlonzo.Code.Category.Monad.Identity.du14)
                                    (coe C80
                                       (coe MAlonzo.Code.Function.du38
                                          (\ v7 -> coe MAlonzo.Code.Function.d68 erased erased)
                                          (coe MAlonzo.Code.Data.Fin.C14 (1 :: Integer))
                                          (coe MAlonzo.Code.Data.Fin.C8 (0 :: Integer))))
                                    (coe MAlonzo.Code.Data.Vec.du192 (2 :: Integer)
                                       (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v4)
                                       (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v5
                                          (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v6
                                             (coe MAlonzo.Code.Data.Vec.C14))))))
                            v2
                            v3))
                  (\ v2 v3 ->
                     coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
                       (\ v4 ->
                          coe du338 v0 v1 v4 (2 :: Integer)
                            (\ v5 v6 ->
                               coe MAlonzo.Code.Data.Product.C30 (coe C92 v5 (coe C86 v5 v6)) v5)
                            (\ v5 v6 ->
                               coe MAlonzo.Code.Data.Product.d28
                                 (coe MAlonzo.Code.Algebra.Structures.d2496
                                    (coe MAlonzo.Code.Algebra.Structures.d2630
                                       (coe MAlonzo.Code.Algebra.Structures.d2798
                                          (coe MAlonzo.Code.Algebra.d1422 v0))))
                                 (coe du130 v0
                                    (coe MAlonzo.Code.Category.Monad.du72
                                       MAlonzo.Code.Category.Monad.Identity.du14)
                                    (coe C80
                                       (coe MAlonzo.Code.Function.du68
                                          (coe MAlonzo.Code.Data.Fin.C8 (1 :: Integer))))
                                    (coe MAlonzo.Code.Data.Vec.du192 (2 :: Integer)
                                       (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v4)
                                       (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v5
                                          (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v6
                                             (coe MAlonzo.Code.Data.Vec.C14)))))
                                 (coe du130 v0
                                    (coe MAlonzo.Code.Category.Monad.du72
                                       MAlonzo.Code.Category.Monad.Identity.du14)
                                    (coe C80
                                       (coe MAlonzo.Code.Function.du38
                                          (\ v7 -> coe MAlonzo.Code.Function.d68 erased erased)
                                          (coe MAlonzo.Code.Data.Fin.C14 (1 :: Integer))
                                          (coe MAlonzo.Code.Data.Fin.C8 (0 :: Integer))))
                                    (coe MAlonzo.Code.Data.Vec.du192 (2 :: Integer)
                                       (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v4)
                                       (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v5
                                          (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v6
                                             (coe MAlonzo.Code.Data.Vec.C14))))))
                            v2
                            v3))))
            (\ v2 v3 v4 ->
               coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
                 (\ v5 ->
                    coe du338 v0 v1 v5 (3 :: Integer)
                      (\ v6 v7 v8 ->
                         coe MAlonzo.Code.Data.Product.C30 (coe C86 (coe C92 v7 v8) v6)
                           (coe C92 (coe C86 v7 v6) (coe C86 v8 v6)))
                      (\ v6 v7 v8 ->
                         coe MAlonzo.Code.Algebra.Structures.d2632
                           (coe MAlonzo.Code.Algebra.Structures.d2798
                              (coe MAlonzo.Code.Algebra.d1422 v0))
                           (coe du130 v0
                              (coe MAlonzo.Code.Category.Monad.du72
                                 MAlonzo.Code.Category.Monad.Identity.du14)
                              (coe C80
                                 (coe MAlonzo.Code.Function.du68
                                    (coe MAlonzo.Code.Data.Fin.C8 (2 :: Integer))))
                              (coe MAlonzo.Code.Data.Vec.du192 (3 :: Integer)
                                 (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v5)
                                 (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) v6
                                    (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v7
                                       (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v8
                                          (coe MAlonzo.Code.Data.Vec.C14))))))
                           (coe du130 v0
                              (coe MAlonzo.Code.Category.Monad.du72
                                 MAlonzo.Code.Category.Monad.Identity.du14)
                              (coe C80
                                 (coe MAlonzo.Code.Function.du38
                                    (\ v9 -> coe MAlonzo.Code.Function.d68 erased erased)
                                    (coe MAlonzo.Code.Data.Fin.C14 (2 :: Integer))
                                    (coe MAlonzo.Code.Data.Fin.C8 (1 :: Integer))))
                              (coe MAlonzo.Code.Data.Vec.du192 (3 :: Integer)
                                 (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v5)
                                 (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) v6
                                    (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v7
                                       (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v8
                                          (coe MAlonzo.Code.Data.Vec.C14))))))
                           (coe du130 v0
                              (coe MAlonzo.Code.Category.Monad.du72
                                 MAlonzo.Code.Category.Monad.Identity.du14)
                              (coe C80
                                 (coe MAlonzo.Code.Function.du38
                                    (\ v9 ->
                                       coe MAlonzo.Code.Function.d38 erased erased erased erased
                                         erased
                                         erased
                                         (\ v10 -> coe MAlonzo.Code.Function.d68 erased erased)
                                         (coe MAlonzo.Code.Data.Fin.C14 (2 :: Integer)))
                                    (coe MAlonzo.Code.Data.Fin.C14 (1 :: Integer))
                                    (coe MAlonzo.Code.Data.Fin.C8 (0 :: Integer))))
                              (coe MAlonzo.Code.Data.Vec.du192 (3 :: Integer)
                                 (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v5)
                                 (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) v6
                                    (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v7
                                       (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v8
                                          (coe MAlonzo.Code.Data.Vec.C14)))))))
                      v2
                      v3
                      v4)))
         (\ v2 ->
            coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
              (\ v3 ->
                 coe du338 v0 v1 v3 (1 :: Integer)
                   (\ v4 ->
                      coe MAlonzo.Code.Data.Product.C30 (coe C86 v4 (coe C96 v4))
                        (coe C98))
                   (\ v4 ->
                      coe MAlonzo.Code.Algebra.Structures.d2800
                        (coe MAlonzo.Code.Algebra.d1422 v0)
                        (coe du130 v0
                           (coe MAlonzo.Code.Category.Monad.du72
                              MAlonzo.Code.Category.Monad.Identity.du14)
                           (coe C80
                              (coe MAlonzo.Code.Function.du68
                                 (coe MAlonzo.Code.Data.Fin.C8 (0 :: Integer))))
                           (coe MAlonzo.Code.Data.Vec.du192 (1 :: Integer)
                              (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v3)
                              (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v4
                                 (coe MAlonzo.Code.Data.Vec.C14)))))
                   v2))
         (\ v2 ->
            coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
              (\ v3 ->
                 coe du338 v0 v1 v3 (1 :: Integer)
                   (\ v4 ->
                      coe MAlonzo.Code.Data.Product.C30 (coe C92 v4 (coe C96 v4))
                        (coe C100))
                   (\ v4 ->
                      coe MAlonzo.Code.Algebra.Structures.d2802
                        (coe MAlonzo.Code.Algebra.d1422 v0)
                        (coe du130 v0
                           (coe MAlonzo.Code.Category.Monad.du72
                              MAlonzo.Code.Category.Monad.Identity.du14)
                           (coe C80
                              (coe MAlonzo.Code.Function.du68
                                 (coe MAlonzo.Code.Data.Fin.C8 (0 :: Integer))))
                           (coe MAlonzo.Code.Data.Vec.du192 (1 :: Integer)
                              (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v3)
                              (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v4
                                 (coe MAlonzo.Code.Data.Vec.C14)))))
                   v2))
         (\ v2 v3 v4 ->
            coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.C46
              (\ v5 ->
                 coe du340 v0 v1 v5 (2 :: Integer)
                   (\ v6 v7 ->
                      coe MAlonzo.Code.Data.Product.C30 (coe C96 v6) (coe C96 v7))
                   v2
                   v3
                   (coe MAlonzo.Code.Algebra.Structures.d2804
                      (coe MAlonzo.Code.Algebra.d1422 v0)
                      (coe MAlonzo.Code.Data.Vec.du696 v5 v2)
                      (coe MAlonzo.Code.Data.Vec.du696 v5 v3)
                      (coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.d44 v4 v5)))))
name306
  = "Algebra.Properties.BooleanAlgebra.Expression._.\10214_\10215Id"
d306 v0 v1 v2 = du306 v1
du306 v0
  = coe d130 erased v0 erased
      (coe MAlonzo.Code.Category.Monad.du72
         MAlonzo.Code.Category.Monad.Identity.du14)
name312
  = "Algebra.Properties.BooleanAlgebra.Expression._.\10214_\10215Vec"
d312 v0 v1 v2 v3 = du312 v1 v3
du312 v0 v1
  = coe d130 erased v0 erased (coe MAlonzo.Code.Data.Vec.du180 v1)
name338 = "Algebra.Properties.BooleanAlgebra.Expression._.R.solve"
d338 v0 v1 v2 v3 v4 = du338 v1 v3 v4
du338 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.Reflection.d110 erased erased
      erased
      erased
      erased
      (coe MAlonzo.Code.Relation.Binary.C85 erased erased
         (coe MAlonzo.Code.Algebra.Structures.d2482
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))))
      (\ v3 -> coe C80)
      (\ v3 v4 v5 ->
         coe MAlonzo.Code.Data.Vec.du696 v2 (coe du312 v0 v1 v3 v4 v5))
      (\ v3 v4 v5 ->
         coe du306 v0 v3 v4
           (coe MAlonzo.Code.Data.Vec.du192 v3
              (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v2)
              v5))
      (\ v3 v4 v5 ->
         coe MAlonzo.Code.Function.du158
           (coe MAlonzo.Code.Relation.Binary.Core.d518
              (coe MAlonzo.Code.Algebra.Structures.d2482
                 (coe MAlonzo.Code.Algebra.Structures.d2630
                    (coe MAlonzo.Code.Algebra.Structures.d2798
                       (coe MAlonzo.Code.Algebra.d1422 v0))))
              (coe MAlonzo.Code.Function.du38
                 (\ v6 ->
                    coe MAlonzo.Code.Category.Applicative.Indexed.d306
                      (coe MAlonzo.Code.Data.Vec.Properties.du136 v2)
                      erased
                      erased
                      erased)
                 (coe du220 v0 (coe MAlonzo.Code.Data.Vec.du180 v1) v3 v4)
                 v5)
              (coe MAlonzo.Code.Function.du38
                 (\ v6 ->
                    coe du224 v0
                      (coe MAlonzo.Code.Category.Monad.du72
                         MAlonzo.Code.Category.Monad.Identity.du14)
                      v3
                      v4)
                 (coe MAlonzo.Code.Data.Vec.d192 erased erased v3 erased erased
                    (coe MAlonzo.Code.Category.Applicative.Indexed.d306
                       (coe MAlonzo.Code.Data.Vec.Properties.du136 v2)
                       erased
                       erased
                       erased))
                 v5))
           (coe MAlonzo.Code.Function.du158
              (coe du38 v0
                 (coe MAlonzo.Code.Function.du38
                    (\ v6 ->
                       coe MAlonzo.Code.Category.Applicative.Indexed.d306
                         (coe MAlonzo.Code.Data.Vec.Properties.du136 v2)
                         erased
                         erased
                         erased)
                    (coe du220 v0 (coe MAlonzo.Code.Data.Vec.du180 v1) v3 v4)
                    v5)
                 (coe MAlonzo.Code.Function.du38
                    (\ v6 ->
                       coe du224 v0
                         (coe MAlonzo.Code.Category.Monad.du72
                            MAlonzo.Code.Category.Monad.Identity.du14)
                         v3
                         v4)
                    (coe MAlonzo.Code.Data.Vec.d192 erased erased v3 erased erased
                       (coe MAlonzo.Code.Category.Applicative.Indexed.d306
                          (coe MAlonzo.Code.Data.Vec.Properties.du136 v2)
                          erased
                          erased
                          erased))
                    v5))
              erased))
name340
  = "Algebra.Properties.BooleanAlgebra.Expression._.R.solve\8321"
d340 v0 v1 v2 v3 v4 = du340 v1 v3 v4
du340 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.Reflection.d126 erased erased
      erased
      erased
      erased
      (coe MAlonzo.Code.Relation.Binary.C85 erased erased
         (coe MAlonzo.Code.Algebra.Structures.d2482
            (coe MAlonzo.Code.Algebra.Structures.d2630
               (coe MAlonzo.Code.Algebra.Structures.d2798
                  (coe MAlonzo.Code.Algebra.d1422 v0)))))
      (\ v3 -> coe C80)
      (\ v3 v4 v5 ->
         coe MAlonzo.Code.Data.Vec.du696 v2 (coe du312 v0 v1 v3 v4 v5))
      (\ v3 v4 v5 ->
         coe du306 v0 v3 v4
           (coe MAlonzo.Code.Data.Vec.du192 v3
              (coe MAlonzo.Code.Data.Vec.d696 erased erased erased v2)
              v5))
      (\ v3 v4 v5 ->
         coe MAlonzo.Code.Function.du158
           (coe MAlonzo.Code.Relation.Binary.Core.d518
              (coe MAlonzo.Code.Algebra.Structures.d2482
                 (coe MAlonzo.Code.Algebra.Structures.d2630
                    (coe MAlonzo.Code.Algebra.Structures.d2798
                       (coe MAlonzo.Code.Algebra.d1422 v0))))
              (coe MAlonzo.Code.Function.du38
                 (\ v6 ->
                    coe MAlonzo.Code.Category.Applicative.Indexed.d306
                      (coe MAlonzo.Code.Data.Vec.Properties.du136 v2)
                      erased
                      erased
                      erased)
                 (coe du220 v0 (coe MAlonzo.Code.Data.Vec.du180 v1) v3 v4)
                 v5)
              (coe MAlonzo.Code.Function.du38
                 (\ v6 ->
                    coe du224 v0
                      (coe MAlonzo.Code.Category.Monad.du72
                         MAlonzo.Code.Category.Monad.Identity.du14)
                      v3
                      v4)
                 (coe MAlonzo.Code.Data.Vec.d192 erased erased v3 erased erased
                    (coe MAlonzo.Code.Category.Applicative.Indexed.d306
                       (coe MAlonzo.Code.Data.Vec.Properties.du136 v2)
                       erased
                       erased
                       erased))
                 v5))
           (coe MAlonzo.Code.Function.du158
              (coe du38 v0
                 (coe MAlonzo.Code.Function.du38
                    (\ v6 ->
                       coe MAlonzo.Code.Category.Applicative.Indexed.d306
                         (coe MAlonzo.Code.Data.Vec.Properties.du136 v2)
                         erased
                         erased
                         erased)
                    (coe du220 v0 (coe MAlonzo.Code.Data.Vec.du180 v1) v3 v4)
                    v5)
                 (coe MAlonzo.Code.Function.du38
                    (\ v6 ->
                       coe du224 v0
                         (coe MAlonzo.Code.Category.Monad.du72
                            MAlonzo.Code.Category.Monad.Identity.du14)
                         v3
                         v4)
                    (coe MAlonzo.Code.Data.Vec.d192 erased erased v3 erased erased
                       (coe MAlonzo.Code.Category.Applicative.Indexed.d306
                          (coe MAlonzo.Code.Data.Vec.Properties.du136 v2)
                          erased
                          erased
                          erased))
                    v5))
              erased))