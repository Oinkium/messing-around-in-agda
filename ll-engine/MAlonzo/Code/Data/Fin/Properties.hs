{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Fin.Properties where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Category.Applicative
import qualified MAlonzo.Code.Category.Applicative.Indexed
import qualified MAlonzo.Code.Category.Functor
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Injection
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary
import qualified MAlonzo.Code.Relation.Nullary.Decidable
name8 = "Data.Fin.Properties._.refl"
d8 v0
  = coe MAlonzo.Code.Relation.Binary.d38
      (coe MAlonzo.Code.Relation.Binary.d268
         (coe MAlonzo.Code.Relation.Binary.d842
            (coe MAlonzo.Code.Relation.Binary.d970
               (coe MAlonzo.Code.Relation.Binary.d1052
                  MAlonzo.Code.Data.Nat.d12))))
      v0
      v0
      (coe MAlonzo.Code.Relation.Binary.Core.d516
         (coe MAlonzo.Code.Relation.Binary.d36
            (coe MAlonzo.Code.Relation.Binary.d268
               (coe MAlonzo.Code.Relation.Binary.d842
                  (coe MAlonzo.Code.Relation.Binary.d970
                     (coe MAlonzo.Code.Relation.Binary.d1052
                        MAlonzo.Code.Data.Nat.d12)))))
         v0)
name16 = "Data.Fin.Properties.drop-suc"
d16 = erased
name18 = "Data.Fin.Properties.preorder"
d18 v0 = du18
du18
  = coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du132
      erased
name22 = "Data.Fin.Properties.setoid"
d22 v0 = du22
du22
  = coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du112
      erased
name26 = "Data.Fin.Properties.strictTotalOrder"
d26 v0 = du26
du26
  = coe MAlonzo.Code.Relation.Binary.C683 erased erased erased
      (coe MAlonzo.Code.Relation.Binary.C561
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
         (\ v0 v1 v2 ->
            coe MAlonzo.Code.Data.Nat.Properties.d608
              (coe MAlonzo.Code.Data.Fin.du18 v0)
              (coe MAlonzo.Code.Data.Fin.du18 v1)
              (coe MAlonzo.Code.Data.Fin.du18 v2))
         (coe d36 erased erased))
name36 = "Data.Fin.Properties._.cmp"
d36 v0 v1 v2 v3 = du36 v2 v3
du36 v0 v1
  = case coe v0 of
        MAlonzo.Code.Data.Fin.C8 v2 -> case coe v1 of
                                           MAlonzo.Code.Data.Fin.C8 v3 -> coe
                                                                            MAlonzo.Code.Relation.Binary.Core.C408
                                                                            erased
                                                                            erased
                                                                            erased
                                           MAlonzo.Code.Data.Fin.C14 v3 v4 -> coe
                                                                                MAlonzo.Code.Relation.Binary.Core.C400
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Nat.Base.C18
                                                                                   (0 :: Integer)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Fin.du18
                                                                                      v4)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Nat.Base.C10
                                                                                      (coe
                                                                                         MAlonzo.Code.Data.Fin.du18
                                                                                         v4)))
                                                                                erased
                                                                                erased
                                           _ -> coe MAlonzo.RTE.mazUnreachableError
        MAlonzo.Code.Data.Fin.C14 v2 v3 -> case coe v1 of
                                               MAlonzo.Code.Data.Fin.C8 v4 -> coe
                                                                                MAlonzo.Code.Relation.Binary.Core.C416
                                                                                erased
                                                                                erased
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Nat.Base.C18
                                                                                   (0 :: Integer)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Fin.du18
                                                                                      v3)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Nat.Base.C10
                                                                                      (coe
                                                                                         MAlonzo.Code.Data.Fin.du18
                                                                                         v3)))
                                               MAlonzo.Code.Data.Fin.C14 v4 v5 -> let v6
                                                                                        = coe du36
                                                                                            v3
                                                                                            v5
                                                                                    in
                                                                                    case coe v6 of
                                                                                        MAlonzo.Code.Relation.Binary.Core.C400
                                                                                          v7 v8
                                                                                          v9 -> coe
                                                                                                  MAlonzo.Code.Relation.Binary.Core.C400
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Nat.Base.C18
                                                                                                     (coe
                                                                                                        ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                                                        (1 ::
                                                                                                           Integer)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Fin.du18
                                                                                                           v3))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Fin.du18
                                                                                                        v5)
                                                                                                     v7)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Function.d38
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     (\ v10
                                                                                                        ->
                                                                                                        v8)
                                                                                                     erased)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Function.d38
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     (\ v10
                                                                                                        ->
                                                                                                        v9)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Base.d250
                                                                                                        erased
                                                                                                        erased))
                                                                                        MAlonzo.Code.Relation.Binary.Core.C408
                                                                                          v7 v8
                                                                                          v9 -> coe
                                                                                                  MAlonzo.Code.Relation.Binary.Core.C408
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Function.d38
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     (\ v10
                                                                                                        ->
                                                                                                        v7)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Base.d250
                                                                                                        erased
                                                                                                        erased))
                                                                                                  erased
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Function.d38
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     (\ v10
                                                                                                        ->
                                                                                                        v9)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Base.d250
                                                                                                        erased
                                                                                                        erased))
                                                                                        MAlonzo.Code.Relation.Binary.Core.C416
                                                                                          v7 v8
                                                                                          v9 -> coe
                                                                                                  MAlonzo.Code.Relation.Binary.Core.C416
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Function.d38
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     (\ v10
                                                                                                        ->
                                                                                                        v7)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Base.d250
                                                                                                        erased
                                                                                                        erased))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Function.d38
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     erased
                                                                                                     (\ v10
                                                                                                        ->
                                                                                                        v8)
                                                                                                     erased)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Nat.Base.C18
                                                                                                     (coe
                                                                                                        ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                                                        (1 ::
                                                                                                           Integer)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Fin.du18
                                                                                                           v5))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Fin.du18
                                                                                                        v3)
                                                                                                     v9)
                                                                                        _ -> coe
                                                                                               MAlonzo.RTE.mazUnreachableError
                                               _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name80 = "Data.Fin.Properties.decSetoid"
d80 v0 = du80
du80 = coe MAlonzo.Code.Relation.Binary.du1250 du26
name86 = "Data.Fin.Properties._\8799_"
d86 v0 = du86
du86
  = coe MAlonzo.Code.Relation.Binary.d184
      (coe MAlonzo.Code.Relation.Binary.d216 du80)
name92 = "Data.Fin.Properties.to-from"
d92 = erased
name100 = "Data.Fin.Properties.from-to"
d100 = erased
name108 = "Data.Fin.Properties.to\8469-strengthen"
d108 = erased
name118 = "Data.Fin.Properties.to\8469-injective"
d118 = erased
name144 = "Data.Fin.Properties.bounded"
d144 v0 v1 = du144 v1
du144 v0
  = case coe v0 of
        MAlonzo.Code.Data.Fin.C8 v1 -> coe MAlonzo.Code.Data.Nat.Base.C18
                                         (0 :: Integer)
                                         v1
                                         (coe MAlonzo.Code.Data.Nat.Base.C10 v1)
        MAlonzo.Code.Data.Fin.C14 v1 v2 -> coe
                                             MAlonzo.Code.Data.Nat.Base.C18
                                             (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                                                (1 :: Integer)
                                                (coe MAlonzo.Code.Data.Fin.du18 v2))
                                             v1
                                             (coe du144 v2)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name152 = "Data.Fin.Properties.prop-to\8469-\8804"
d152 v0 v1 = du152 v1
du152 v0
  = case coe v0 of
        MAlonzo.Code.Data.Fin.C8 v1 -> coe MAlonzo.Code.Data.Nat.Base.C10
                                         (coe MAlonzo.Code.Data.Nat.Base.d180
                                            (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                                               (1 :: Integer)
                                               v1))
        MAlonzo.Code.Data.Fin.C14 v1 v2 -> coe
                                             MAlonzo.Code.Data.Nat.Base.C18
                                             (coe MAlonzo.Code.Data.Fin.du18 v2)
                                             (coe MAlonzo.Code.Data.Nat.Base.d180 v1)
                                             (coe du152 v2)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name162 = "Data.Fin.Properties.prop-to\8469-\8804\8242"
d162 v0 v1 = du162 v1
du162 v0
  = coe MAlonzo.Code.Data.Nat.Properties.du530 (coe du144 v0)
name167 = "Data.Fin.Properties._..absurdlambda"
d167 = erased
name170 = "Data.Fin.Properties.n\8469-\8469i\8804n"
d170 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.Fin.C8 v2 -> coe d8
                                         (coe MAlonzo.Code.Data.Fin.d276 v0
                                            (coe MAlonzo.Code.Data.Fin.C8 v0))
        MAlonzo.Code.Data.Fin.C14 v2 v3 -> let v4
                                                 = coe
                                                     ((Prelude.-) :: Integer -> Integer -> Integer)
                                                     v0
                                                     (1 :: Integer)
                                             in
                                             coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                               (coe MAlonzo.Code.Data.Nat.d76
                                                  (coe MAlonzo.Code.Data.Fin.d276 v4 v3)
                                                  v4
                                                  v0
                                                  (coe d170 v4 v3)
                                                  (coe MAlonzo.Code.Data.Nat.d76 v4 v0 v0
                                                     (coe MAlonzo.Code.Data.Nat.Properties.d486 v4)
                                                     (coe MAlonzo.Code.Data.Nat.d70 v0)))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name188 = "Data.Fin.Properties.inject-lemma"
d188 = erased
name202 = "Data.Fin.Properties.inject+-lemma"
d202 = erased
name209 = "Data.Fin.Properties._..absurdlambda"
d209 = erased
name214 = "Data.Fin.Properties.inject\8321-lemma"
d214 = erased
name226 = "Data.Fin.Properties.inject\8804-lemma"
d226 = erased
name240 = "Data.Fin.Properties.inject\8804-refl"
d240 = erased
name246 = "Data.Fin.Properties.\8826\8658<\8242"
d246 v0 v1 v2 = du246 v2
du246 v0
  = case coe v0 of
        MAlonzo.Code.Data.Fin.C304 v1 v2 -> coe
                                              MAlonzo.Code.Data.Nat.Properties.du422
                                              v1
                                              (coe du144 v2)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name252 = "Data.Fin.Properties.<\8242\8658\8826"
d252 v0 v1 v2 = du252 v0 v2
du252 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.Nat.Base.C68 -> coe
                                            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du28
                                            (coe MAlonzo.Code.Data.Fin.C304
                                               (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                                                  (1 :: Integer)
                                                  v0)
                                               (coe MAlonzo.Code.Data.Fin.d30 v0))
        MAlonzo.Code.Data.Nat.Base.C74 v2 v3 -> let v4 = coe du252 v0 v3 in
                                                  case coe v4 of
                                                      MAlonzo.Code.Data.Fin.C304 v5 v6 -> coe
                                                                                            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du28
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Fin.C304
                                                                                               (coe
                                                                                                  ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                                                  (1 ::
                                                                                                     Integer)
                                                                                                  v5)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Fin.du128
                                                                                                  v6))
                                                      _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name263 = "Data.Fin.Properties._..absurdlambda"
d263 = erased
name278 = "Data.Fin.Properties.to\8469-raise"
d278 = erased
name292 = "Data.Fin.Properties.from\8469\8804-to\8469"
d292 = erased
name304 = "Data.Fin.Properties.to\8469-from\8469\8804"
d304 = erased
name310 = "Data.Fin.Properties.from\8469-def"
d310 = erased
name317 = "Data.Fin.Properties._..absurdlambda"
d317 = erased
name322
  = "Data.Fin.Properties.from\8469\8804\8801from\8469\8804\8243"
d322 = erased
name334 = "Data.Fin.Properties._+\8242_"
d334 v0 v1 v2 v3
  = coe MAlonzo.Code.Data.Fin.du136
      (coe MAlonzo.Code.Data.Fin.du240 v1 v2 v3)
      (coe MAlonzo.Code.Data.Nat.Properties.d1156
         (coe MAlonzo.Code.Data.Fin.du18 v2)
         (coe MAlonzo.Code.Data.Nat.Base.d180 v0)
         v1
         v1
         (coe du152 v2)
         (coe d8 v1))
name342 = "Data.Fin.Properties.reverse"
d342 v0 v1
  = let v2
          = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
              (1 :: Integer)
      in
      coe MAlonzo.Code.Data.Fin.du136
        (coe MAlonzo.Code.Data.Fin.d266 v2 v1)
        (coe MAlonzo.Code.Data.Nat.Properties.d548
           (coe MAlonzo.Code.Data.Fin.du18 v1)
           v0)
name352 = "Data.Fin.Properties.reverse-prop"
d352 = erased
name366 = "Data.Fin.Properties._.to\8469\8255\8469-"
d366 = erased
name376 = "Data.Fin.Properties.reverse-involutive"
d376 = erased
name388 = "Data.Fin.Properties._._.comm"
d388 = erased
name394 = "Data.Fin.Properties._.lem\8321"
d394 = erased
name408 = "Data.Fin.Properties._.lem\8322"
d408 = erased
name409 = "Data.Fin.Properties._..absurdlambda"
d409 = erased
name420 = "Data.Fin.Properties._._.decompose-n"
d420 v0 v1 v2 v3 = du420 v2 v3
du420 v0 v1
  = coe MAlonzo.Code.Data.Product.C30
      (coe MAlonzo.Code.Agda.Builtin.Nat.d22 v0
         (coe MAlonzo.Code.Data.Fin.du18 v1))
      erased
name422 = "Data.Fin.Properties._._.j"
d422 v0 v1 v2 v3 = du422 v2 v3
du422 v0 v1 = coe MAlonzo.Code.Data.Product.d26 (coe du420 v0 v1)
name424 = "Data.Fin.Properties._._.i+j\8801k"
d424 = erased
name428 = "Data.Fin.Properties._.eq"
d428 = erased
name431 = "Data.Fin.Properties._..absurdlambda"
d431 = erased
name436 = "Data.Fin.Properties.reverse-suc"
d436 = erased
name452 = "Data.Fin.Properties.eq?"
d452 v0 v1 v2 v3 = du452 v3
du452 v0
  = coe MAlonzo.Code.Relation.Nullary.Decidable.d128 erased erased
      erased
      erased
      erased
      erased
      v0
      du86
name466 = "Data.Fin.Properties.sequence"
d466 v0 v1 v2 v3 = du466 v1 v2 v3
du466 v0 v1 v2 = coe d504 erased erased erased v2 v0 v1
name480 = "Data.Fin.Properties._._._<$>_"
d480 v0 v1 v2 v3 = du480 v3
du480 v0 = coe MAlonzo.Code.Category.Applicative.du26 v0
name504 = "Data.Fin.Properties._.helper"
d504 v0 v1 v2 v3 v4 v5 v6 = du504 v3 v4 v5 v6
du504 v0 v1 v2 v3
  = case coe v1 of
        0 -> coe MAlonzo.Code.Category.Applicative.Indexed.d56 v0 erased ()
               erased
        _ -> let v4
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Category.Applicative.Indexed.d68 v0 erased erased
                 erased
                 ()
                 ()
                 (coe du480 v0 erased erased
                    (coe v2 (coe MAlonzo.Code.Data.Fin.C8 v4))
                    ()
                    (coe d524 erased erased erased erased erased erased erased)
                    (coe v3 (coe MAlonzo.Code.Data.Fin.C8 v4)))
                 (coe du504 v0 v4
                    (\ v5 -> coe v2 (coe MAlonzo.Code.Data.Fin.C14 v4 v5))
                    (coe MAlonzo.Code.Function.d38 erased erased erased erased erased
                       erased
                       (\ v5 -> v3)
                       (coe MAlonzo.Code.Data.Fin.C14 v4)))
name524 = "Data.Fin.Properties._._.combine"
d524 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du524 v7 v8 v9
du524 v0 v1 v2
  = case coe v2 of
        MAlonzo.Code.Data.Fin.C8 v3 -> coe v0
        MAlonzo.Code.Data.Fin.C14 v3 v4 -> coe v1 v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name4409 = "Data.Fin.Properties._..absurdlambda"
d4409 = erased