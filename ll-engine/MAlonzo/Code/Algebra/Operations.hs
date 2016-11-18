{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.Operations where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
name44 = "Algebra.Operations._.identity"
d44 v0 v1 v2 = du44 v2
du44 v0 = coe MAlonzo.Code.Algebra.du668 v0
name80 = "Algebra.Operations._.reflexive"
d80 v0 v1 v2 = du80 v2
du80 v0 = coe MAlonzo.Code.Algebra.du688 v0
name86 = "Algebra.Operations._.setoid"
d86 v0 v1 v2 = du86 v2
du86 v0 = coe MAlonzo.Code.Algebra.du714 v0
name96 = "Algebra.Operations._._\8718"
d96 v0 v1 v2 = du96 v2
du96 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe du86 v0)
name98 = "Algebra.Operations._._\8764\10216_\10217_"
d98 v0 v1 v2 = du98 v2
du98 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40 (coe du86 v0)
name112 = "Algebra.Operations._\215_"
d112 v0 v1 v2 v3 v4 = du112 v2 v3 v4
du112 v0 v1 v2
  = case coe v1 of
        0 -> coe MAlonzo.Code.Algebra.d644 v0
        _ -> let v3
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in coe MAlonzo.Code.Algebra.d640 v0 v2 (coe du112 v0 v3 v2)
name120 = "Algebra.Operations._\215\8242_"
d120 v0 v1 v2 v3 v4 = du120 v2 v3 v4
du120 v0 v1 v2
  = case coe v1 of
        0 -> coe MAlonzo.Code.Algebra.d644 v0
        _ -> let v3
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in
               let v4 = coe MAlonzo.Code.Algebra.d640 v0 v2 (coe du120 v0 v3 v2)
                 in
                 case coe v3 of
                     0 -> coe v2
                     _ -> coe v4
name130 = "Algebra.Operations._^_"
d130 v0 v1 v2 v3 v4 = du130 v2 v3 v4
du130 v0 v1 v2
  = case coe v2 of
        0 -> coe MAlonzo.Code.Algebra.d646 v0
        _ -> let v3
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v2
                       (1 :: Integer)
               in coe MAlonzo.Code.Algebra.d642 v0 v1 (coe du130 v0 v1 v3)
name142 = "Algebra.Operations.1+\215\8242"
d142 v0 v1 v2 v3 v4 = du142 v2 v3 v4
du142 v0 v1 v2
  = case coe v1 of
        0 -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
               (coe du98 v0 v2
                  (coe MAlonzo.Code.Algebra.d640 v0 v2
                     (coe MAlonzo.Code.Algebra.d644 v0))
                  (coe MAlonzo.Code.Algebra.d640 v0 v2
                     (coe MAlonzo.Code.Algebra.d644 v0))
                  (coe MAlonzo.Code.Function.du158
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d124
                           (coe MAlonzo.Code.Algebra.Structures.d406
                              (coe MAlonzo.Code.Algebra.Structures.d1246
                                 (coe MAlonzo.Code.Algebra.Structures.d1416
                                    (coe MAlonzo.Code.Algebra.d648 v0)))))
                        (coe MAlonzo.Code.Algebra.d640 v0 v2
                           (coe MAlonzo.Code.Algebra.d644 v0))
                        v2)
                     (coe MAlonzo.Code.Data.Product.d28 (coe du44 v0) v2))
                  (coe du96 v0
                     (coe MAlonzo.Code.Algebra.d640 v0 v2
                        (coe MAlonzo.Code.Algebra.d644 v0))))
        _ -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
               (coe du96 v0
                  (coe MAlonzo.Code.Algebra.d640 v0 v2 (coe du120 v0 v1 v2)))
name154 = "Algebra.Operations.\215\8776\215\8242"
d154 v0 v1 v2 v3 v4 = du154 v2 v3 v4
du154 v0 v1 v2
  = case coe v1 of
        0 -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
               (coe du96 v0 (coe MAlonzo.Code.Algebra.d644 v0))
        _ -> let v3
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                 (coe du98 v0
                    (coe MAlonzo.Code.Algebra.d640 v0 v2 (coe du112 v0 v3 v2))
                    (coe MAlonzo.Code.Algebra.d640 v0 v2 (coe du120 v0 v3 v2))
                    (coe du120 v0 v1 v2)
                    (coe MAlonzo.Code.Algebra.Structures.d128
                       (coe MAlonzo.Code.Algebra.Structures.d406
                          (coe MAlonzo.Code.Algebra.Structures.d1246
                             (coe MAlonzo.Code.Algebra.Structures.d1416
                                (coe MAlonzo.Code.Algebra.d648 v0))))
                       v2
                       v2
                       (coe du112 v0 v3 v2)
                       (coe du120 v0 v3 v2)
                       (coe MAlonzo.Code.Relation.Binary.Core.d516
                          (coe MAlonzo.Code.Algebra.Structures.d124
                             (coe MAlonzo.Code.Algebra.Structures.d406
                                (coe MAlonzo.Code.Algebra.Structures.d1246
                                   (coe MAlonzo.Code.Algebra.Structures.d1416
                                      (coe MAlonzo.Code.Algebra.d648 v0)))))
                          v2)
                       (coe du154 v0 v3 v2))
                    (coe du98 v0
                       (coe MAlonzo.Code.Algebra.d640 v0 v2 (coe du120 v0 v3 v2))
                       (coe du120 v0 v1 v2)
                       (coe du120 v0 v1 v2)
                       (coe MAlonzo.Code.Function.du158
                          (coe MAlonzo.Code.Relation.Binary.Core.d518
                             (coe MAlonzo.Code.Algebra.Structures.d124
                                (coe MAlonzo.Code.Algebra.Structures.d406
                                   (coe MAlonzo.Code.Algebra.Structures.d1246
                                      (coe MAlonzo.Code.Algebra.Structures.d1416
                                         (coe MAlonzo.Code.Algebra.d648 v0)))))
                             (coe du120 v0 v1 v2)
                             (coe MAlonzo.Code.Algebra.d640 v0 v2 (coe du120 v0 v3 v2)))
                          (coe du142 v0 v3 v2))
                       (coe du96 v0 (coe du120 v0 v1 v2))))
name168 = "Algebra.Operations.\215-homo-+"
d168 v0 v1 v2 v3 v4 v5 = du168 v2 v3 v4 v5
du168 v0 v1 v2 v3
  = case coe v2 of
        0 -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
               (coe du98 v0 (coe du112 v0 v3 v1)
                  (coe MAlonzo.Code.Algebra.d640 v0
                     (coe MAlonzo.Code.Algebra.d644 v0)
                     (coe du112 v0 v3 v1))
                  (coe MAlonzo.Code.Algebra.d640 v0
                     (coe MAlonzo.Code.Algebra.d644 v0)
                     (coe du112 v0 v3 v1))
                  (coe MAlonzo.Code.Function.du158
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d124
                           (coe MAlonzo.Code.Algebra.Structures.d406
                              (coe MAlonzo.Code.Algebra.Structures.d1246
                                 (coe MAlonzo.Code.Algebra.Structures.d1416
                                    (coe MAlonzo.Code.Algebra.d648 v0)))))
                        (coe MAlonzo.Code.Algebra.d640 v0
                           (coe MAlonzo.Code.Algebra.d644 v0)
                           (coe du112 v0 v3 v1))
                        (coe du112 v0 v3 v1))
                     (coe MAlonzo.Code.Data.Product.d26 (coe du44 v0)
                        (coe du112 v0 v3 v1)))
                  (coe du96 v0
                     (coe MAlonzo.Code.Algebra.d640 v0
                        (coe MAlonzo.Code.Algebra.d644 v0)
                        (coe du112 v0 v3 v1))))
        _ -> let v4
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v2
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                 (coe du98 v0
                    (coe MAlonzo.Code.Algebra.d640 v0 v1
                       (coe du112 v0
                          (coe ((Prelude.+) :: Integer -> Integer -> Integer) v4 v3)
                          v1))
                    (coe MAlonzo.Code.Algebra.d640 v0 v1
                       (coe MAlonzo.Code.Algebra.d640 v0 (coe du112 v0 v4 v1)
                          (coe du112 v0 v3 v1)))
                    (coe MAlonzo.Code.Algebra.d640 v0
                       (coe MAlonzo.Code.Algebra.d640 v0 v1 (coe du112 v0 v4 v1))
                       (coe du112 v0 v3 v1))
                    (coe MAlonzo.Code.Algebra.Structures.d128
                       (coe MAlonzo.Code.Algebra.Structures.d406
                          (coe MAlonzo.Code.Algebra.Structures.d1246
                             (coe MAlonzo.Code.Algebra.Structures.d1416
                                (coe MAlonzo.Code.Algebra.d648 v0))))
                       v1
                       v1
                       (coe du112 v0
                          (coe ((Prelude.+) :: Integer -> Integer -> Integer) v4 v3)
                          v1)
                       (coe MAlonzo.Code.Algebra.d640 v0 (coe du112 v0 v4 v1)
                          (coe du112 v0 v3 v1))
                       (coe MAlonzo.Code.Relation.Binary.Core.d516
                          (coe MAlonzo.Code.Algebra.Structures.d124
                             (coe MAlonzo.Code.Algebra.Structures.d406
                                (coe MAlonzo.Code.Algebra.Structures.d1246
                                   (coe MAlonzo.Code.Algebra.Structures.d1416
                                      (coe MAlonzo.Code.Algebra.d648 v0)))))
                          v1)
                       (coe du168 v0 v1 v4 v3))
                    (coe du98 v0
                       (coe MAlonzo.Code.Algebra.d640 v0 v1
                          (coe MAlonzo.Code.Algebra.d640 v0 (coe du112 v0 v4 v1)
                             (coe du112 v0 v3 v1)))
                       (coe MAlonzo.Code.Algebra.d640 v0
                          (coe MAlonzo.Code.Algebra.d640 v0 v1 (coe du112 v0 v4 v1))
                          (coe du112 v0 v3 v1))
                       (coe MAlonzo.Code.Algebra.d640 v0
                          (coe MAlonzo.Code.Algebra.d640 v0 v1 (coe du112 v0 v4 v1))
                          (coe du112 v0 v3 v1))
                       (coe MAlonzo.Code.Function.du158
                          (coe MAlonzo.Code.Relation.Binary.Core.d518
                             (coe MAlonzo.Code.Algebra.Structures.d124
                                (coe MAlonzo.Code.Algebra.Structures.d406
                                   (coe MAlonzo.Code.Algebra.Structures.d1246
                                      (coe MAlonzo.Code.Algebra.Structures.d1416
                                         (coe MAlonzo.Code.Algebra.d648 v0)))))
                             (coe MAlonzo.Code.Algebra.d640 v0
                                (coe MAlonzo.Code.Algebra.d640 v0 v1 (coe du112 v0 v4 v1))
                                (coe du112 v0 v3 v1))
                             (coe MAlonzo.Code.Algebra.d640 v0 v1
                                (coe MAlonzo.Code.Algebra.d640 v0 (coe du112 v0 v4 v1)
                                   (coe du112 v0 v3 v1))))
                          (coe MAlonzo.Code.Algebra.Structures.d126
                             (coe MAlonzo.Code.Algebra.Structures.d406
                                (coe MAlonzo.Code.Algebra.Structures.d1246
                                   (coe MAlonzo.Code.Algebra.Structures.d1416
                                      (coe MAlonzo.Code.Algebra.d648 v0))))
                             v1
                             (coe du112 v0 v4 v1)
                             (coe du112 v0 v3 v1)))
                       (coe du96 v0
                          (coe MAlonzo.Code.Algebra.d640 v0
                             (coe MAlonzo.Code.Algebra.d640 v0 v1 (coe du112 v0 v4 v1))
                             (coe du112 v0 v3 v1)))))
name186 = "Algebra.Operations.\215\8242-homo-+"
d186 v0 v1 v2 v3 v4 v5 = du186 v2 v3 v4 v5
du186 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du98 v0
         (coe du120 v0
            (coe ((Prelude.+) :: Integer -> Integer -> Integer) v2 v3)
            v1)
         (coe du112 v0
            (coe ((Prelude.+) :: Integer -> Integer -> Integer) v2 v3)
            v1)
         (coe MAlonzo.Code.Algebra.d640 v0 (coe du120 v0 v2 v1)
            (coe du120 v0 v3 v1))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d124
                  (coe MAlonzo.Code.Algebra.Structures.d406
                     (coe MAlonzo.Code.Algebra.Structures.d1246
                        (coe MAlonzo.Code.Algebra.Structures.d1416
                           (coe MAlonzo.Code.Algebra.d648 v0)))))
               (coe du112 v0
                  (coe ((Prelude.+) :: Integer -> Integer -> Integer) v2 v3)
                  v1)
               (coe du120 v0
                  (coe ((Prelude.+) :: Integer -> Integer -> Integer) v2 v3)
                  v1))
            (coe du154 v0
               (coe ((Prelude.+) :: Integer -> Integer -> Integer) v2 v3)
               v1))
         (coe du98 v0
            (coe du112 v0
               (coe ((Prelude.+) :: Integer -> Integer -> Integer) v2 v3)
               v1)
            (coe MAlonzo.Code.Algebra.d640 v0 (coe du112 v0 v2 v1)
               (coe du112 v0 v3 v1))
            (coe MAlonzo.Code.Algebra.d640 v0 (coe du120 v0 v2 v1)
               (coe du120 v0 v3 v1))
            (coe du168 v0 v1 v2 v3)
            (coe du98 v0
               (coe MAlonzo.Code.Algebra.d640 v0 (coe du112 v0 v2 v1)
                  (coe du112 v0 v3 v1))
               (coe MAlonzo.Code.Algebra.d640 v0 (coe du120 v0 v2 v1)
                  (coe du120 v0 v3 v1))
               (coe MAlonzo.Code.Algebra.d640 v0 (coe du120 v0 v2 v1)
                  (coe du120 v0 v3 v1))
               (coe MAlonzo.Code.Algebra.Structures.d128
                  (coe MAlonzo.Code.Algebra.Structures.d406
                     (coe MAlonzo.Code.Algebra.Structures.d1246
                        (coe MAlonzo.Code.Algebra.Structures.d1416
                           (coe MAlonzo.Code.Algebra.d648 v0))))
                  (coe du112 v0 v2 v1)
                  (coe du120 v0 v2 v1)
                  (coe du112 v0 v3 v1)
                  (coe du120 v0 v3 v1)
                  (coe du154 v0 v2 v1)
                  (coe du154 v0 v3 v1))
               (coe du96 v0
                  (coe MAlonzo.Code.Algebra.d640 v0 (coe du120 v0 v2 v1)
                     (coe du120 v0 v3 v1))))))
name198 = "Algebra.Operations.\215\&1-homo-*"
d198 v0 v1 v2 v3 v4 = du198 v2 v3 v4
du198 v0 v1 v2
  = case coe v1 of
        0 -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
               (coe du98 v0 (coe MAlonzo.Code.Algebra.d644 v0)
                  (coe MAlonzo.Code.Algebra.d642 v0
                     (coe MAlonzo.Code.Algebra.d644 v0)
                     (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                  (coe MAlonzo.Code.Algebra.d642 v0
                     (coe MAlonzo.Code.Algebra.d644 v0)
                     (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                  (coe MAlonzo.Code.Function.du158
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe MAlonzo.Code.Algebra.Structures.d124
                           (coe MAlonzo.Code.Algebra.Structures.d406
                              (coe MAlonzo.Code.Algebra.Structures.d1246
                                 (coe MAlonzo.Code.Algebra.Structures.d1416
                                    (coe MAlonzo.Code.Algebra.d648 v0)))))
                        (coe MAlonzo.Code.Algebra.d642 v0
                           (coe MAlonzo.Code.Algebra.d644 v0)
                           (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                        (coe MAlonzo.Code.Algebra.d644 v0))
                     (coe MAlonzo.Code.Data.Product.d26
                        (coe MAlonzo.Code.Algebra.Structures.d1418
                           (coe MAlonzo.Code.Algebra.d648 v0))
                        (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))))
                  (coe du96 v0
                     (coe MAlonzo.Code.Algebra.d642 v0
                        (coe MAlonzo.Code.Algebra.d644 v0)
                        (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))))
        _ -> let v3
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                 (coe du98 v0
                    (coe du112 v0
                       (coe ((Prelude.+) :: Integer -> Integer -> Integer) v2
                          (coe ((Prelude.*) :: Integer -> Integer -> Integer) v3 v2))
                       (coe MAlonzo.Code.Algebra.d646 v0))
                    (coe MAlonzo.Code.Algebra.d640 v0
                       (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                       (coe du112 v0
                          (coe ((Prelude.*) :: Integer -> Integer -> Integer) v3 v2)
                          (coe MAlonzo.Code.Algebra.d646 v0)))
                    (coe MAlonzo.Code.Algebra.d642 v0
                       (coe MAlonzo.Code.Algebra.d640 v0
                          (coe MAlonzo.Code.Algebra.d646 v0)
                          (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0)))
                       (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                    (coe du168 v0 (coe MAlonzo.Code.Algebra.d646 v0) v2
                       (coe ((Prelude.*) :: Integer -> Integer -> Integer) v3 v2))
                    (coe du98 v0
                       (coe MAlonzo.Code.Algebra.d640 v0
                          (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                          (coe du112 v0
                             (coe ((Prelude.*) :: Integer -> Integer -> Integer) v3 v2)
                             (coe MAlonzo.Code.Algebra.d646 v0)))
                       (coe MAlonzo.Code.Algebra.d640 v0
                          (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                          (coe MAlonzo.Code.Algebra.d642 v0
                             (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                             (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))))
                       (coe MAlonzo.Code.Algebra.d642 v0
                          (coe MAlonzo.Code.Algebra.d640 v0
                             (coe MAlonzo.Code.Algebra.d646 v0)
                             (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0)))
                          (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                       (coe MAlonzo.Code.Algebra.Structures.d128
                          (coe MAlonzo.Code.Algebra.Structures.d406
                             (coe MAlonzo.Code.Algebra.Structures.d1246
                                (coe MAlonzo.Code.Algebra.Structures.d1416
                                   (coe MAlonzo.Code.Algebra.d648 v0))))
                          (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                          (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                          (coe du112 v0
                             (coe ((Prelude.*) :: Integer -> Integer -> Integer) v3 v2)
                             (coe MAlonzo.Code.Algebra.d646 v0))
                          (coe MAlonzo.Code.Algebra.d642 v0
                             (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                             (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                          (coe MAlonzo.Code.Relation.Binary.Core.d516
                             (coe MAlonzo.Code.Algebra.Structures.d124
                                (coe MAlonzo.Code.Algebra.Structures.d406
                                   (coe MAlonzo.Code.Algebra.Structures.d1246
                                      (coe MAlonzo.Code.Algebra.Structures.d1416
                                         (coe MAlonzo.Code.Algebra.d648 v0)))))
                             (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                          (coe du198 v0 v3 v2))
                       (coe du98 v0
                          (coe MAlonzo.Code.Algebra.d640 v0
                             (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                             (coe MAlonzo.Code.Algebra.d642 v0
                                (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                                (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))))
                          (coe MAlonzo.Code.Algebra.d640 v0
                             (coe MAlonzo.Code.Algebra.d642 v0
                                (coe MAlonzo.Code.Algebra.d646 v0)
                                (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                             (coe MAlonzo.Code.Algebra.d642 v0
                                (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                                (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))))
                          (coe MAlonzo.Code.Algebra.d642 v0
                             (coe MAlonzo.Code.Algebra.d640 v0
                                (coe MAlonzo.Code.Algebra.d646 v0)
                                (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0)))
                             (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                          (coe MAlonzo.Code.Function.du158
                             (coe MAlonzo.Code.Relation.Binary.Core.d518
                                (coe MAlonzo.Code.Algebra.Structures.d124
                                   (coe MAlonzo.Code.Algebra.Structures.d406
                                      (coe MAlonzo.Code.Algebra.Structures.d1246
                                         (coe MAlonzo.Code.Algebra.Structures.d1416
                                            (coe MAlonzo.Code.Algebra.d648 v0)))))
                                (coe MAlonzo.Code.Algebra.d640 v0
                                   (coe MAlonzo.Code.Algebra.d642 v0
                                      (coe MAlonzo.Code.Algebra.d646 v0)
                                      (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                                   (coe MAlonzo.Code.Algebra.d642 v0
                                      (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                                      (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))))
                                (coe MAlonzo.Code.Algebra.d640 v0
                                   (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                                   (coe MAlonzo.Code.Algebra.d642 v0
                                      (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                                      (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))))
                             (coe MAlonzo.Code.Algebra.Structures.d128
                                (coe MAlonzo.Code.Algebra.Structures.d406
                                   (coe MAlonzo.Code.Algebra.Structures.d1246
                                      (coe MAlonzo.Code.Algebra.Structures.d1416
                                         (coe MAlonzo.Code.Algebra.d648 v0))))
                                (coe MAlonzo.Code.Algebra.d642 v0
                                   (coe MAlonzo.Code.Algebra.d646 v0)
                                   (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                                (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                                (coe MAlonzo.Code.Algebra.d642 v0
                                   (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                                   (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                                (coe MAlonzo.Code.Algebra.d642 v0
                                   (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                                   (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                                (coe MAlonzo.Code.Data.Product.d26
                                   (coe MAlonzo.Code.Algebra.Structures.d264
                                      (coe MAlonzo.Code.Algebra.Structures.d1248
                                         (coe MAlonzo.Code.Algebra.Structures.d1416
                                            (coe MAlonzo.Code.Algebra.d648 v0))))
                                   (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                                (coe MAlonzo.Code.Relation.Binary.Core.d516
                                   (coe MAlonzo.Code.Algebra.Structures.d124
                                      (coe MAlonzo.Code.Algebra.Structures.d406
                                         (coe MAlonzo.Code.Algebra.Structures.d1246
                                            (coe MAlonzo.Code.Algebra.Structures.d1416
                                               (coe MAlonzo.Code.Algebra.d648 v0)))))
                                   (coe MAlonzo.Code.Algebra.d642 v0
                                      (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                                      (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))))))
                          (coe du98 v0
                             (coe MAlonzo.Code.Algebra.d640 v0
                                (coe MAlonzo.Code.Algebra.d642 v0
                                   (coe MAlonzo.Code.Algebra.d646 v0)
                                   (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                                (coe MAlonzo.Code.Algebra.d642 v0
                                   (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                                   (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))))
                             (coe MAlonzo.Code.Algebra.d642 v0
                                (coe MAlonzo.Code.Algebra.d640 v0
                                   (coe MAlonzo.Code.Algebra.d646 v0)
                                   (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0)))
                                (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                             (coe MAlonzo.Code.Algebra.d642 v0
                                (coe MAlonzo.Code.Algebra.d640 v0
                                   (coe MAlonzo.Code.Algebra.d646 v0)
                                   (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0)))
                                (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                             (coe MAlonzo.Code.Function.du158
                                (coe MAlonzo.Code.Relation.Binary.Core.d518
                                   (coe MAlonzo.Code.Algebra.Structures.d124
                                      (coe MAlonzo.Code.Algebra.Structures.d406
                                         (coe MAlonzo.Code.Algebra.Structures.d1246
                                            (coe MAlonzo.Code.Algebra.Structures.d1416
                                               (coe MAlonzo.Code.Algebra.d648 v0)))))
                                   (coe MAlonzo.Code.Algebra.d642 v0
                                      (coe MAlonzo.Code.Algebra.d640 v0
                                         (coe MAlonzo.Code.Algebra.d646 v0)
                                         (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0)))
                                      (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                                   (coe MAlonzo.Code.Algebra.d640 v0
                                      (coe MAlonzo.Code.Algebra.d642 v0
                                         (coe MAlonzo.Code.Algebra.d646 v0)
                                         (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
                                      (coe MAlonzo.Code.Algebra.d642 v0
                                         (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))
                                         (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))))
                                (coe MAlonzo.Code.Data.Product.d28
                                   (coe MAlonzo.Code.Algebra.Structures.d1250
                                      (coe MAlonzo.Code.Algebra.Structures.d1416
                                         (coe MAlonzo.Code.Algebra.d648 v0)))
                                   (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                                   (coe MAlonzo.Code.Algebra.d646 v0)
                                   (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0))))
                             (coe du96 v0
                                (coe MAlonzo.Code.Algebra.d642 v0
                                   (coe MAlonzo.Code.Algebra.d640 v0
                                      (coe MAlonzo.Code.Algebra.d646 v0)
                                      (coe du112 v0 v3 (coe MAlonzo.Code.Algebra.d646 v0)))
                                   (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))))))))
name210 = "Algebra.Operations.\215\8242\&1-homo-*"
d210 v0 v1 v2 v3 v4 = du210 v2 v3 v4
du210 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du98 v0
         (coe du120 v0
            (coe ((Prelude.*) :: Integer -> Integer -> Integer) v1 v2)
            (coe MAlonzo.Code.Algebra.d646 v0))
         (coe du112 v0
            (coe ((Prelude.*) :: Integer -> Integer -> Integer) v1 v2)
            (coe MAlonzo.Code.Algebra.d646 v0))
         (coe MAlonzo.Code.Algebra.d642 v0
            (coe du120 v0 v1 (coe MAlonzo.Code.Algebra.d646 v0))
            (coe du120 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d124
                  (coe MAlonzo.Code.Algebra.Structures.d406
                     (coe MAlonzo.Code.Algebra.Structures.d1246
                        (coe MAlonzo.Code.Algebra.Structures.d1416
                           (coe MAlonzo.Code.Algebra.d648 v0)))))
               (coe du112 v0
                  (coe ((Prelude.*) :: Integer -> Integer -> Integer) v1 v2)
                  (coe MAlonzo.Code.Algebra.d646 v0))
               (coe du120 v0
                  (coe ((Prelude.*) :: Integer -> Integer -> Integer) v1 v2)
                  (coe MAlonzo.Code.Algebra.d646 v0)))
            (coe du154 v0
               (coe ((Prelude.*) :: Integer -> Integer -> Integer) v1 v2)
               (coe MAlonzo.Code.Algebra.d646 v0)))
         (coe du98 v0
            (coe du112 v0
               (coe ((Prelude.*) :: Integer -> Integer -> Integer) v1 v2)
               (coe MAlonzo.Code.Algebra.d646 v0))
            (coe MAlonzo.Code.Algebra.d642 v0
               (coe du112 v0 v1 (coe MAlonzo.Code.Algebra.d646 v0))
               (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
            (coe MAlonzo.Code.Algebra.d642 v0
               (coe du120 v0 v1 (coe MAlonzo.Code.Algebra.d646 v0))
               (coe du120 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
            (coe du198 v0 v1 v2)
            (coe du98 v0
               (coe MAlonzo.Code.Algebra.d642 v0
                  (coe du112 v0 v1 (coe MAlonzo.Code.Algebra.d646 v0))
                  (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
               (coe MAlonzo.Code.Algebra.d642 v0
                  (coe du120 v0 v1 (coe MAlonzo.Code.Algebra.d646 v0))
                  (coe du120 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
               (coe MAlonzo.Code.Algebra.d642 v0
                  (coe du120 v0 v1 (coe MAlonzo.Code.Algebra.d646 v0))
                  (coe du120 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
               (coe MAlonzo.Code.Algebra.Structures.d128
                  (coe MAlonzo.Code.Algebra.Structures.d262
                     (coe MAlonzo.Code.Algebra.Structures.d1248
                        (coe MAlonzo.Code.Algebra.Structures.d1416
                           (coe MAlonzo.Code.Algebra.d648 v0))))
                  (coe du112 v0 v1 (coe MAlonzo.Code.Algebra.d646 v0))
                  (coe du120 v0 v1 (coe MAlonzo.Code.Algebra.d646 v0))
                  (coe du112 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                  (coe du120 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0))
                  (coe du154 v0 v1 (coe MAlonzo.Code.Algebra.d646 v0))
                  (coe du154 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))
               (coe du96 v0
                  (coe MAlonzo.Code.Algebra.d642 v0
                     (coe du120 v0 v1 (coe MAlonzo.Code.Algebra.d646 v0))
                     (coe du120 v0 v2 (coe MAlonzo.Code.Algebra.d646 v0)))))))
name216 = "Algebra.Operations.\215-cong"
d216 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du216 v2 v3 v4 v5 v6 v8
du216 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du98 v0 (coe du112 v0 v1 v3) (coe du112 v0 v2 v3)
         (coe du112 v0 v2 v4)
         (coe MAlonzo.Code.Function.du158
            (coe du80 v0 (coe du112 v0 v1 v3) (coe du112 v0 v2 v3))
            erased)
         (coe du98 v0 (coe du112 v0 v2 v3) (coe du112 v0 v2 v4)
            (coe du112 v0 v2 v4)
            (coe du236 v0 v2 v3 v4 v5)
            (coe du96 v0 (coe du112 v0 v2 v4))))
name236 = "Algebra.Operations._.\215-cong\691"
d236 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du236 v2 v9 v10 v11 v12
du236 v0 v1 v2 v3 v4
  = case coe v1 of
        0 -> coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d124
                  (coe MAlonzo.Code.Algebra.Structures.d406
                     (coe MAlonzo.Code.Algebra.Structures.d1246
                        (coe MAlonzo.Code.Algebra.Structures.d1416
                           (coe MAlonzo.Code.Algebra.d648 v0)))))
               (coe du112 v0 (0 :: Integer) v2)
        _ -> let v5
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Function.du176 v4
                 (coe MAlonzo.Code.Algebra.Structures.d128
                    (coe MAlonzo.Code.Algebra.Structures.d406
                       (coe MAlonzo.Code.Algebra.Structures.d1246
                          (coe MAlonzo.Code.Algebra.Structures.d1416
                             (coe MAlonzo.Code.Algebra.d648 v0))))
                    v2
                    v3
                    (coe du112 v0 v5 v2)
                    (coe du112 v0 v5 v3))
                 (coe du236 v0 v5 v2 v3 v4)
name246 = "Algebra.Operations.\215\8242-cong"
d246 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du246 v2 v3 v4 v5 v6 v8
du246 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du98 v0 (coe du120 v0 v1 v3) (coe du112 v0 v1 v3)
         (coe du120 v0 v2 v4)
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe MAlonzo.Code.Algebra.Structures.d124
                  (coe MAlonzo.Code.Algebra.Structures.d406
                     (coe MAlonzo.Code.Algebra.Structures.d1246
                        (coe MAlonzo.Code.Algebra.Structures.d1416
                           (coe MAlonzo.Code.Algebra.d648 v0)))))
               (coe du112 v0 v1 v3)
               (coe du120 v0 v1 v3))
            (coe du154 v0 v1 v3))
         (coe du98 v0 (coe du112 v0 v1 v3) (coe du112 v0 v2 v4)
            (coe du120 v0 v2 v4)
            (coe du216 v0 v1 v2 v3 v4 v5)
            (coe du98 v0 (coe du112 v0 v2 v4) (coe du120 v0 v2 v4)
               (coe du120 v0 v2 v4)
               (coe du154 v0 v2 v4)
               (coe du96 v0 (coe du120 v0 v2 v4)))))
name260 = "Algebra.Operations.^-cong"
d260 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du260 v2 v3 v4 v5 v6 v7
du260 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du98 v0 (coe du130 v0 v1 v3) (coe du130 v0 v1 v4)
         (coe du130 v0 v2 v4)
         (coe MAlonzo.Code.Function.du158
            (coe du80 v0 (coe du130 v0 v1 v3) (coe du130 v0 v1 v4))
            erased)
         (coe du98 v0 (coe du130 v0 v1 v4) (coe du130 v0 v2 v4)
            (coe du130 v0 v2 v4)
            (coe du282 v0 v4 v1 v2 v5)
            (coe du96 v0 (coe du130 v0 v2 v4))))
name282 = "Algebra.Operations._.^-cong\737"
d282 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du282 v2 v9 v10 v11 v12
du282 v0 v1 v2 v3 v4
  = case coe v1 of
        0 -> coe MAlonzo.Code.Relation.Binary.Core.d516
               (coe MAlonzo.Code.Algebra.Structures.d124
                  (coe MAlonzo.Code.Algebra.Structures.d406
                     (coe MAlonzo.Code.Algebra.Structures.d1246
                        (coe MAlonzo.Code.Algebra.Structures.d1416
                           (coe MAlonzo.Code.Algebra.d648 v0)))))
               (coe du130 v0 v2 (0 :: Integer))
        _ -> let v5
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Function.du176 v4
                 (coe MAlonzo.Code.Algebra.Structures.d128
                    (coe MAlonzo.Code.Algebra.Structures.d262
                       (coe MAlonzo.Code.Algebra.Structures.d1248
                          (coe MAlonzo.Code.Algebra.Structures.d1416
                             (coe MAlonzo.Code.Algebra.d648 v0))))
                    v2
                    v3
                    (coe du130 v0 v2 v5)
                    (coe du130 v0 v3 v5))
                 (coe du282 v0 v5 v2 v3 v4)