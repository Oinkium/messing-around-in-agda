{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Nat where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Injection
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PartialOrderReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary
import qualified MAlonzo.Code.Relation.Nullary.Decidable
name8 = "Data.Nat.eq?"
d8 v0 v1 v2 = du8 v2
du8 v0
  = coe MAlonzo.Code.Relation.Nullary.Decidable.d128 erased erased
      erased
      erased
      erased
      erased
      v0
      MAlonzo.Code.Data.Nat.Base.d220
name12 = "Data.Nat.decTotalOrder"
d12
  = coe MAlonzo.Code.Relation.Binary.C531 erased erased erased
      (coe MAlonzo.Code.Relation.Binary.C507
         (coe MAlonzo.Code.Relation.Binary.C459
            (coe MAlonzo.Code.Relation.Binary.C217
               (coe MAlonzo.Code.Relation.Binary.C17
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
                  d18
                  d36)
               erased)
            d42)
         MAlonzo.Code.Data.Nat.Base.d220
         MAlonzo.Code.Data.Nat.Base.d254)
name18 = "Data.Nat._.refl\8242"
d18 v0 v1 v2 = du18 v0
du18 v0
  = case coe v0 of
        0 -> coe MAlonzo.Code.Data.Nat.Base.C10 (0 :: Integer)
        _ -> let v1
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in coe MAlonzo.Code.Data.Nat.Base.C18 v1 v1 (coe du18 v1)
name22 = "Data.Nat._.antisym"
d22 = erased
name36 = "Data.Nat._.trans"
d36 v0 v1 v2 v3 v4 = du36 v2 v3 v4
du36 v0 v1 v2
  = case coe v1 of
        MAlonzo.Code.Data.Nat.Base.C10 v3 -> coe
                                               MAlonzo.Code.Data.Nat.Base.C10
                                               v0
        MAlonzo.Code.Data.Nat.Base.C18 v3 v4 v5 -> case coe v2 of
                                                       MAlonzo.Code.Data.Nat.Base.C18 v6 v7
                                                         v8 -> coe MAlonzo.Code.Data.Nat.Base.C18 v3
                                                                 v7
                                                                 (coe du36 v7 v5 v8)
                                                       _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name42 = "Data.Nat._.total"
d42 v0 v1
  = let v2 = coe Right (coe MAlonzo.Code.Data.Nat.Base.C10 v0) in
      case coe v0 of
          0 -> coe Left (coe MAlonzo.Code.Data.Nat.Base.C10 v1)
          _ | ((Prelude.>=) :: Integer -> Integer -> Bool) v0 (1 :: Integer)
              ->
              let v3
                    = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                        (1 :: Integer)
                in
                case coe v1 of
                    0 -> coe Right (coe MAlonzo.Code.Data.Nat.Base.C10 v0)
                    _ | ((Prelude.>=) :: Integer -> Integer -> Bool) v1 (1 :: Integer)
                        ->
                        let v4
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                  (1 :: Integer)
                          in
                          let v5 = coe d42 v3 v4 in
                            case coe v5 of
                                Left v6 -> coe Left (coe MAlonzo.Code.Data.Nat.Base.C18 v3 v4 v6)
                                Right v6 -> coe Right (coe MAlonzo.Code.Data.Nat.Base.C18 v4 v3 v6)
                                _ -> coe MAlonzo.RTE.mazUnreachableError
                    _ -> coe v2
          _ -> coe v2
name68 = "Data.Nat.\8804-Reasoning._._IsRelatedTo_"
d68 a0 a1 = ()
name70 = "Data.Nat.\8804-Reasoning._._\8718"
d70 v0
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.C56
      (coe MAlonzo.Code.Relation.Binary.d38
         (coe MAlonzo.Code.Relation.Binary.d268
            (coe MAlonzo.Code.Relation.Binary.d842
               (coe MAlonzo.Code.Relation.Binary.d970
                  (coe MAlonzo.Code.Relation.Binary.d1052 d12))))
         v0
         v0
         (coe MAlonzo.Code.Relation.Binary.Core.d516
            (coe MAlonzo.Code.Relation.Binary.d36
               (coe MAlonzo.Code.Relation.Binary.d268
                  (coe MAlonzo.Code.Relation.Binary.d842
                     (coe MAlonzo.Code.Relation.Binary.d970
                        (coe MAlonzo.Code.Relation.Binary.d1052 d12)))))
            v0))
name72 = "Data.Nat.\8804-Reasoning._._\8776\10216\10217_"
d72 v0 v1 v2 = du72 v2
du72 v0 = coe v0
name74 = "Data.Nat.\8804-Reasoning._._\8776\10216_\10217_"
d74
  = coe MAlonzo.Code.Relation.Binary.PartialOrderReasoning.du56
      (coe MAlonzo.Code.Relation.Binary.C235 erased erased erased
         (coe MAlonzo.Code.Relation.Binary.d842
            (coe MAlonzo.Code.Relation.Binary.d970
               (coe MAlonzo.Code.Relation.Binary.d1052 d12))))
name76 = "Data.Nat.\8804-Reasoning._._\8764\10216_\10217_"
d76
  = coe MAlonzo.Code.Relation.Binary.PartialOrderReasoning.du60
      (coe MAlonzo.Code.Relation.Binary.C235 erased erased erased
         (coe MAlonzo.Code.Relation.Binary.d842
            (coe MAlonzo.Code.Relation.Binary.d970
               (coe MAlonzo.Code.Relation.Binary.d1052 d12))))
name78 = "Data.Nat.\8804-Reasoning._.begin_"
d78 v0 v1 = du78
du78 = MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
name92 = "Data.Nat.\8804-Reasoning._<\10216_\10217_"
d92 v0 v1 v2 v3 v4
  = coe d76
      (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
         v0)
      v1
      v2
      v3
      v4