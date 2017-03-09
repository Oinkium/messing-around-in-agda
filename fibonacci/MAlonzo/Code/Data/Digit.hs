{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Digit where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Algebra.RingSolver
import qualified
       MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing
import qualified MAlonzo.Code.Data.Char
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.DivMod
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Vec
import qualified MAlonzo.Code.Data.Vec.NZ45Zary
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Induction.Nat
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified MAlonzo.Code.Relation.Binary.Reflection
import qualified MAlonzo.Code.Relation.Nullary.Decidable
name10 = "Data.Digit.lem"
d10 v0 v1 v2
  = coe MAlonzo.Code.Function.du158
      (coe MAlonzo.Code.Data.Nat.Properties.d422 erased
         (coe ((Prelude.+) :: Integer -> Integer -> Integer)
            (coe ((Prelude.*) :: Integer -> Integer -> Integer)
               (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                  v0)
               (coe ((Prelude.+) :: Integer -> Integer -> Integer) (2 :: Integer)
                  v1))
            v2))
      (coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
         (coe MAlonzo.Code.Data.Nat.d76
            (coe ((Prelude.+) :: Integer -> Integer -> Integer) (2 :: Integer)
               v0)
            (coe ((Prelude.+) :: Integer -> Integer -> Integer)
               (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                  (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                     (coe ((Prelude.+) :: Integer -> Integer -> Integer) (2 :: Integer)
                        (coe ((Prelude.*) :: Integer -> Integer -> Integer)
                           (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                              v0)
                           v1))
                     v0)
                  v0)
               v2)
            (coe ((Prelude.+) :: Integer -> Integer -> Integer)
               (coe ((Prelude.*) :: Integer -> Integer -> Integer)
                  (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                     v0)
                  (coe ((Prelude.+) :: Integer -> Integer -> Integer) (2 :: Integer)
                     v1))
               v2)
            (coe MAlonzo.Code.Data.Nat.Properties.d444
               (coe ((Prelude.+) :: Integer -> Integer -> Integer) (2 :: Integer)
                  v0)
               (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                  (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                     (coe ((Prelude.*) :: Integer -> Integer -> Integer)
                        (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                           v0)
                        v1)
                     v0)
                  v2))
            (coe MAlonzo.Code.Data.Nat.d74
               (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                  (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                     (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                        (coe ((Prelude.+) :: Integer -> Integer -> Integer) (2 :: Integer)
                           (coe ((Prelude.*) :: Integer -> Integer -> Integer)
                              (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                                 v0)
                              v1))
                        v0)
                     v0)
                  v2)
               (coe MAlonzo.Code.Data.Vec.NZ45Zary.du66
                  (coe MAlonzo.Code.Data.Vec.NZ45Zary.du46 (3 :: Integer)
                     (coe MAlonzo.Code.Algebra.RingSolver.d316 erased erased erased
                        erased
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
                           MAlonzo.Code.Data.Nat.Properties.d62)
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du568
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
                              MAlonzo.Code.Data.Nat.Properties.d62))
                        erased
                        erased
                        (coe MAlonzo.Code.Data.Product.d28
                           (coe MAlonzo.Code.Relation.Binary.Reflection.du100
                              (\ v3 -> coe MAlonzo.Code.Algebra.RingSolver.C284)
                              (3 :: Integer)
                              (\ v3 v4 v5 ->
                                 coe MAlonzo.Code.Data.Nat.Properties.d92 (3 :: Integer)
                                   (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                                      (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                                         (coe MAlonzo.Code.Algebra.RingSolver.C280 (2 :: Integer))
                                         v3)
                                      (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                                         (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer) v3
                                            (coe MAlonzo.Code.Data.Nat.Properties.d86 (3 :: Integer)
                                               (coe MAlonzo.Code.Data.Nat.Properties.d88
                                                  (3 :: Integer)
                                                  (coe MAlonzo.Code.Algebra.RingSolver.C280
                                                     (1 :: Integer))
                                                  v3)
                                               v5))
                                         v4))
                                   (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer) v4
                                      (coe MAlonzo.Code.Data.Nat.Properties.d86 (3 :: Integer)
                                         (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                                            (coe MAlonzo.Code.Algebra.RingSolver.C280
                                               (1 :: Integer))
                                            v3)
                                         (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                                            (coe MAlonzo.Code.Algebra.RingSolver.C280
                                               (2 :: Integer))
                                            v5))))))))
                  (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) v0
                     (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) v2
                        (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) v1
                           (coe MAlonzo.Code.Data.Vec.C14)))))
               (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                  (coe ((Prelude.*) :: Integer -> Integer -> Integer)
                     (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                        v0)
                     (coe ((Prelude.+) :: Integer -> Integer -> Integer) (2 :: Integer)
                        v1))
                  v2)
               (coe MAlonzo.Code.Data.Nat.Properties.d188 (3 :: Integer)
                  (\ v3 v4 v5 ->
                     coe MAlonzo.Code.Data.Nat.Properties.d92 (3 :: Integer)
                       (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                          (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                             (coe MAlonzo.Code.Algebra.RingSolver.C280 (2 :: Integer))
                             v3)
                          (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                             (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer) v3
                                (coe MAlonzo.Code.Data.Nat.Properties.d86 (3 :: Integer)
                                   (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                                      (coe MAlonzo.Code.Algebra.RingSolver.C280 (1 :: Integer))
                                      v3)
                                   v5))
                             v4))
                       (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer) v4
                          (coe MAlonzo.Code.Data.Nat.Properties.d86 (3 :: Integer)
                             (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                                (coe MAlonzo.Code.Algebra.RingSolver.C280 (1 :: Integer))
                                v3)
                             (coe MAlonzo.Code.Data.Nat.Properties.d88 (3 :: Integer)
                                (coe MAlonzo.Code.Algebra.RingSolver.C280 (2 :: Integer))
                                v5))))
                  erased
                  v0
                  v2
                  v1)
               (coe MAlonzo.Code.Data.Nat.d70
                  (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                     (coe ((Prelude.*) :: Integer -> Integer -> Integer)
                        (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                           v0)
                        (coe ((Prelude.+) :: Integer -> Integer -> Integer) (2 :: Integer)
                           v1))
                     v2)))))
name24 = "Data.Digit.Digit"
d24 = erased
name28 = "Data.Digit.Decimal"
d28 = erased
name30 = "Data.Digit.Bit"
d30 = erased
name32 = "Data.Digit.0b"
d32 = coe MAlonzo.Code.Data.Fin.C8 (1 :: Integer)
name34 = "Data.Digit.1b"
d34
  = coe MAlonzo.Code.Data.Fin.C14 (1 :: Integer)
      (coe MAlonzo.Code.Data.Fin.C8 (0 :: Integer))
name36 = "Data.Digit.digitChars"
d36
  = coe MAlonzo.Code.Data.Vec.C22 (15 :: Integer) '0'
      (coe MAlonzo.Code.Data.Vec.C22 (14 :: Integer) '1'
         (coe MAlonzo.Code.Data.Vec.C22 (13 :: Integer) '2'
            (coe MAlonzo.Code.Data.Vec.C22 (12 :: Integer) '3'
               (coe MAlonzo.Code.Data.Vec.C22 (11 :: Integer) '4'
                  (coe MAlonzo.Code.Data.Vec.C22 (10 :: Integer) '5'
                     (coe MAlonzo.Code.Data.Vec.C22 (9 :: Integer) '6'
                        (coe MAlonzo.Code.Data.Vec.C22 (8 :: Integer) '7'
                           (coe MAlonzo.Code.Data.Vec.C22 (7 :: Integer) '8'
                              (coe MAlonzo.Code.Data.Vec.C22 (6 :: Integer) '9'
                                 (coe MAlonzo.Code.Data.Vec.C22 (5 :: Integer) 'a'
                                    (coe MAlonzo.Code.Data.Vec.C22 (4 :: Integer) 'b'
                                       (coe MAlonzo.Code.Data.Vec.C22 (3 :: Integer) 'c'
                                          (coe MAlonzo.Code.Data.Vec.C22 (2 :: Integer) 'd'
                                             (coe MAlonzo.Code.Data.Vec.C22 (1 :: Integer) 'e'
                                                (coe MAlonzo.Code.Data.Vec.C22 (0 :: Integer) 'f'
                                                   (coe MAlonzo.Code.Data.Vec.C14))))))))))))))))
name42 = "Data.Digit.showDigit"
d42 v0 v1 v2 = du42 v0 v2
du42 v0 v1
  = coe MAlonzo.Code.Data.Vec.du696
      (coe MAlonzo.Code.Data.Fin.du136 v1
         (coe MAlonzo.Code.Relation.Nullary.Decidable.du34
            (coe MAlonzo.Code.Data.Nat.Base.d254 v0 (16 :: Integer))))
      d36
name50 = "Data.Digit.fromDigits"
d50 v0 v1
  = case coe v1 of
        [] -> 0 :: Integer
        (:) v2 v3 -> coe ((Prelude.+) :: Integer -> Integer -> Integer)
                       (coe MAlonzo.Code.Data.Fin.du18 v2)
                       (coe ((Prelude.*) :: Integer -> Integer -> Integer) (coe d50 v0 v3)
                          v0)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name66 = "Data.Digit.toDigits"
d66 v0 v1 v2 = du66 v0 v2
du66 v0 v1
  = let v2
          = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
              (2 :: Integer)
      in
      coe MAlonzo.Code.Induction.Nat.du94 erased
        (coe d100 v2 erased erased)
        v1
name76 = "Data.Digit._.base"
d76 v0 v1 v2 = du76 v0
du76 v0
  = coe ((Prelude.+) :: Integer -> Integer -> Integer) (2 :: Integer)
      v0
name78 = "Data.Digit._.Pred"
d78 = erased
name88 = "Data.Digit._.cons"
d88 v0 v1 v2 v3 v4 v5 = du88 v4 v5
du88 v0 v1
  = coe MAlonzo.Code.Data.Product.C30
      (coe (:) v0 (coe MAlonzo.Code.Data.Product.d26 v1))
      erased
name100 = "Data.Digit._.helper"
d100 v0 v1 v2 v3 v4 = du100 v0 v3 v4
du100 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Data.Nat.DivMod.du160 v1 (coe du76 v0)
      in
      case coe v3 of
          MAlonzo.Code.Data.Nat.DivMod.C28 v4 v5 v6 -> case coe v4 of
                                                           0 -> coe MAlonzo.Code.Data.Product.C30
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Base.du10
                                                                     v5)
                                                                  erased
                                                           _ -> coe du88 v5
                                                                  (coe v2 v4
                                                                     (coe d10
                                                                        (coe
                                                                           MAlonzo.Code.Data.Nat.Base.d180
                                                                           v4)
                                                                        v0
                                                                        (coe
                                                                           MAlonzo.Code.Data.Fin.du18
                                                                           v5)))
          _ -> coe MAlonzo.RTE.mazUnreachableError