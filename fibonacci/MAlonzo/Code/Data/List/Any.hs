{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.List.Any where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Equivalence
import qualified MAlonzo.Code.Function.Related
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.InducedPreorders
import qualified MAlonzo.Code.Relation.Binary.List.Pointwise
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Unary
name14 = "Data.List.Any.Any"
d14 a0 a1 a2 a3 a4 = ()

data T14 a0 a1 a2 = C30 a0 a1 a2
                  | C38 a0 a1 a2
name52 = "Data.List.Any.map"
d52 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du52 v6 v8
du52 v0 v1
  = case coe v1 of
        C30 v2 v3 v4 -> coe C30 v2 v3 (coe v0 v2 v4)
        C38 v2 v3 v4 -> coe C38 v2 v3 (coe du52 v0 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name74 = "Data.List.Any.tail"
d74 v0 v1 v2 v3 v4 v5 v6 v7 = du74 v7
du74 v0
  = case coe v0 of
        C30 v1 v2 v3 -> coe MAlonzo.Code.Data.Empty.d10 () erased erased
        C38 v1 v2 v3 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name92 = "Data.List.Any.any"
d92 v0 v1 v2 v3 v4 v5 = du92 v4 v5
du92 v0 v1
  = case coe v1 of
        [] -> coe MAlonzo.Code.Relation.Nullary.C26 erased
        (:) v2 v3 -> let v4 = coe v0 v2 in
                       case coe v4 of
                           MAlonzo.Code.Relation.Nullary.C22 v5 -> coe
                                                                     MAlonzo.Code.Relation.Nullary.C22
                                                                     (coe C30 v2 v3 v5)
                           MAlonzo.Code.Relation.Nullary.C26 v5 -> coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.du98
                                                                     erased
                                                                     erased
                                                                     (coe C38 v2 v3)
                                                                     (coe d74 erased erased erased
                                                                        erased
                                                                        erased
                                                                        erased
                                                                        erased)
                                                                     (coe du92 v0 v3)
                           _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name132 = "Data.List.Any.index"
d132 v0 v1 v2 v3 v4 v5 = du132 v5
du132 v0
  = case coe v0 of
        C30 v1 v2 v3 -> coe MAlonzo.Code.Data.Fin.C8
                          (coe MAlonzo.Code.Data.List.Base.du144
                             (\ v4 v5 ->
                                coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                                  v5)
                             (0 :: Integer)
                             v2)
        C38 v1 v2 v3 -> coe MAlonzo.Code.Data.Fin.C14
                          (coe MAlonzo.Code.Data.List.Base.du226 v2)
                          (coe du132 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name170 = "Data.List.Any.Membership.LS._\8776_"
d170 = erased
name194 = "Data.List.Any.Membership.lift-resp"
d194 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du194 v5 v8 v9
du194 v0 v1 v2
  = case coe v1 of
        MAlonzo.Code.Relation.Binary.List.Pointwise.C48 v3 v4 v5 v6 v7
          v8 -> case coe v2 of
                    C30 v9 v10 v11 -> coe C30 v5 v6 (coe v0 v3 v5 v7 v11)
                    C38 v9 v10 v11 -> coe C38 v5 v6 (coe du194 v0 v8 v11)
                    _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name214 = "Data.List.Any.Membership._\8712_"
d214 = erased
name220 = "Data.List.Any.Membership._\8713_"
d220 = erased
name226 = "Data.List.Any.Membership._\8838_"
d226 = erased
name234 = "Data.List.Any.Membership._\8840_"
d234 = erased
name242 = "Data.List.Any.Membership.\8712-resp-\8776"
d242 v0 v1 v2 v3 v4 v5 = du242 v2 v3 v4 v5
du242 v0 v1 v2 v3
  = coe MAlonzo.Code.Function.d138 erased erased erased erased erased
      erased
      (coe MAlonzo.Code.Relation.Binary.Core.d520
         (coe MAlonzo.Code.Relation.Binary.d136 v0)
         v1
         v2
         v3)
name246 = "Data.List.Any.Membership.\8712-resp-list-\8776"
d246 v0 v1 v2 v3 = du246 v2 v3
du246 v0 v1
  = coe d194 erased erased erased erased erased
      (coe d242 erased erased v0 v1)
name248 = "Data.List.Any.Membership.\8838-preorder"
d248 v0 v1 v2 = du248 v2
du248 v0
  = coe MAlonzo.Code.Relation.Binary.C67 erased erased
      (\ v1 v2 -> ())
      (coe MAlonzo.Code.Relation.Binary.C17
         (coe MAlonzo.Code.Relation.Binary.d136
            (coe MAlonzo.Code.Relation.Binary.List.Pointwise.du634 v0))
         (\ v1 v2 v3 v4 -> coe du246 v0 v4 v1 v2 v3)
         (\ v1 v2 v3 v4 v5 v6 ->
            coe MAlonzo.Code.Function.d38 erased erased erased erased erased
              erased
              (\ v7 -> coe v5 v6)
              (coe v4 v6)))
name254
  = "Data.List.Any.Membership.\8838-Reasoning._._IsRelatedTo_"
d254 a0 a1 a2 a3 a4 = ()
name256 = "Data.List.Any.Membership.\8838-Reasoning._._\8718"
d256 v0 v1 v2 v3 = du256 v2 v3
du256 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.C56
      (coe MAlonzo.Code.Relation.Binary.d38
         (coe MAlonzo.Code.Relation.Binary.d92 (coe du248 v0))
         v1
         v1
         (coe MAlonzo.Code.Relation.Binary.Core.d516
            (coe MAlonzo.Code.Relation.Binary.d36
               (coe MAlonzo.Code.Relation.Binary.d92 (coe du248 v0)))
            v1))
name258
  = "Data.List.Any.Membership.\8838-Reasoning._._\8776\10216_\10217_"
d258 v0 v1 v2 = du258 v2
du258 v0
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d84 erased
      erased
      erased
      (coe du248 v0)
name260
  = "Data.List.Any.Membership.\8838-Reasoning._._\8776\10216\10217_"
d260 v0 v1 v2 = du260 v2
du260 v0 = coe v0
name262
  = "Data.List.Any.Membership.\8838-Reasoning._._\8764\10216_\10217_"
d262 v0 v1 v2 = du262 v2
du262 v0
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d72 erased
      erased
      erased
      (coe du248 v0)
name264 = "Data.List.Any.Membership.\8838-Reasoning._.begin_"
d264 v0 v1 = du264
du264 = MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
name278
  = "Data.List.Any.Membership.\8838-Reasoning._\8712\10216_\10217_"
d278 v0 v1 v2 v3 v4 v5 = du278 v1 v4 v5
du278 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62 v2 v0 v1
name294 = "Data.List.Any.Membership.map-with-\8712"
d294 v0 v1 v2 v3 v4 v5 v6 = du294 v2 v5 v6
du294 v0 v1 v2
  = case coe v1 of
        [] -> coe []
        (:) v3 v4 -> coe (:)
                       (coe v2 v3
                          (coe C30 v3 v4
                             (coe MAlonzo.Code.Relation.Binary.Core.d516
                                (coe MAlonzo.Code.Relation.Binary.d136 v0)
                                v3)))
                       (coe du294 v0 v4
                          (\ v5 ->
                             coe MAlonzo.Code.Function.d38 erased erased erased erased erased
                               erased
                               (\ v6 -> coe v2 v5)
                               (coe C38 v3 v4)))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name312 = "Data.List.Any.Membership.find"
d312 v0 v1 v2 v3 v4 v5 v6 = du312 v2 v6
du312 v0 v1
  = case coe v1 of
        C30 v2 v3 v4 -> coe MAlonzo.Code.Data.Product.C30 v2
                          (coe MAlonzo.Code.Data.Product.C30
                             (coe C30 v2 v3
                                (coe MAlonzo.Code.Relation.Binary.Core.d516
                                   (coe MAlonzo.Code.Relation.Binary.d136 v0)
                                   v2))
                             v4)
        C38 v2 v3 v4 -> coe MAlonzo.Code.Data.Product.du188
                          (coe MAlonzo.Code.Function.d68 erased erased)
                          (\ v5 ->
                             coe MAlonzo.Code.Data.Product.d188 erased erased erased erased
                               erased
                               erased
                               erased
                               erased
                               (coe C38 v2 v3)
                               (\ v6 -> coe MAlonzo.Code.Function.d68 erased erased))
                          (coe du312 v0 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name326 = "Data.List.Any.Membership.lose"
d326 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du326 v5 v7 v8 v9
du326 v0 v1 v2 v3
  = coe du52
      (\ v4 ->
         coe MAlonzo.Code.Function.d138 erased erased erased erased erased
           erased
           (coe v1 v0 v4)
           v3)
      v2
name342 = "Data.List.Any.Membership-\8801.M._\8712_"
d342 = erased
name344 = "Data.List.Any.Membership-\8801.M._\8713_"
d344 = erased
name346 = "Data.List.Any.Membership-\8801.M._\8838_"
d346 = erased
name348 = "Data.List.Any.Membership-\8801.M._\8840_"
d348 = erased
name350 = "Data.List.Any.Membership-\8801.M.find"
d350 v0 v1 = du350 v1
du350 v0
  = coe d312 erased erased
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du112 v0)
name354 = "Data.List.Any.Membership-\8801.M.lose"
d354 v0 v1 = du354
du354 = coe d326 erased erased erased
name356 = "Data.List.Any.Membership-\8801.M.map-with-\8712"
d356 v0 v1 = du356 v1
du356 v0
  = coe d294 erased erased
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du112 v0)
name358 = "Data.List.Any.Membership-\8801.M.\8712-resp-list-\8776"
d358 v0 v1 = du358 v1
du358 v0
  = coe d246 erased erased
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du112 v0)
name360 = "Data.List.Any.Membership-\8801.M.\8712-resp-\8776"
d360 = erased
name398 = "Data.List.Any.Membership-\8801.lose"
d398 v0 v1 v2 v3 v4 v5 = du398 v1 v3 v4 v5
du398 v0 v1 v2 v3
  = coe du354 v0 v1 v2 v3
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.d28
         erased
         erased
         erased
         erased)
name404 = "Data.List.Any.Membership-\8801.\8838-preorder"
d404 v0 v1 = du404
du404
  = coe MAlonzo.Code.Relation.Binary.C67 erased erased
      (\ v0 v1 -> ())
      (coe MAlonzo.Code.Relation.Binary.C17
         (coe MAlonzo.Code.Relation.Binary.d136
            (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du112
               erased))
         (\ v0 v1 v2 v3 ->
            coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.d28
              erased
              erased
              erased
              erased
              erased
              erased
              erased)
         (\ v0 v1 v2 v3 v4 v5 ->
            coe MAlonzo.Code.Function.d38 erased erased erased erased erased
              erased
              (\ v6 -> coe v4 v5)
              (coe v3 v5)))
name410 = "Data.List.Any.Membership-\8801.[_]-Order"
d410 v0 v1 v2 = du410 v0 v1
du410 v0 v1
  = coe MAlonzo.Code.Function.Related.du528 v0 v1 erased erased
name418 = "Data.List.Any.Membership-\8801.[_]-Equality"
d418 v0 v1 v2 = du418 v0 v1
du418 v0 v1
  = coe MAlonzo.Code.Function.Related.du586 v0 v1 erased erased
name428 = "Data.List.Any.Membership-\8801._\8764[_]_"
d428 = erased
name448 = "Data.List.Any.Membership-\8801.bag-=\8658"
d448 v0 v1 v2 v3 v4 v5 v6 = du448 v0 v1 v5 v6
du448 v0 v1 v2 v3
  = coe MAlonzo.Code.Function.Related.d130 v0 v1 v1 erased erased
      (coe v2 v3)
name460
  = "Data.List.Any.Membership-\8801.\8838-Reasoning.PR._IsRelatedTo_"
d460 a0 a1 a2 a3 = ()
name462
  = "Data.List.Any.Membership-\8801.\8838-Reasoning.PR._\8718"
d462 v0 v1 v2 = du462 v2
du462 v0
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.C56
      (coe MAlonzo.Code.Relation.Binary.d38
         (coe MAlonzo.Code.Relation.Binary.d92 du404)
         v0
         v0
         (coe MAlonzo.Code.Relation.Binary.Core.d516
            (coe MAlonzo.Code.Relation.Binary.d36
               (coe MAlonzo.Code.Relation.Binary.d92 du404))
            v0))
name464
  = "Data.List.Any.Membership-\8801.\8838-Reasoning.PR._\8764\10216_\10217_"
d464 v0 v1 = du464
du464
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d72 erased
      erased
      erased
      du404
name466
  = "Data.List.Any.Membership-\8801.\8838-Reasoning.PR._\8776\10216_\10217_"
d466 v0 v1 = du466
du466
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d84 erased
      erased
      erased
      du404
name468
  = "Data.List.Any.Membership-\8801.\8838-Reasoning.PR._\8776\10216\10217_"
d468 v0 v1 v2 = du468 v2
du468 v0 = coe v0
name470
  = "Data.List.Any.Membership-\8801.\8838-Reasoning.PR.begin_"
d470 v0 v1 = du470
du470 = MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
name488
  = "Data.List.Any.Membership-\8801.\8838-Reasoning._\8712\10216_\10217_"
d488 v0 v1 v2 v3 v4 v5 v6 = du488 v2 v5 v6
du488 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62 v2 v0 v1
name508
  = "Data.List.Any.Membership-\8801.\8838-Reasoning._\8764\10216_\10217_"
d508 v0 v1 v2 v3 v4 v5 v6 v7 = du508 v0 v1 v3 v4 v5 v6 v7
du508 v0 v1 v2 v3 v4 v5 v6
  = coe du464 v2 v3 v4
      (\ v7 ->
         coe MAlonzo.Code.Function.Related.d176 v0 v1 v1 erased erased
           (coe v5 v7))
      v6
name526 = "Data.List.Any.satisfied"
d526 v0 v1 v2 v3 v4 = du526 v1 v2 v3 v4
du526 v0 v1 v2 v3
  = coe MAlonzo.Code.Function.d38 erased erased erased erased erased
      erased
      (\ v4 ->
         coe MAlonzo.Code.Data.Product.d188 erased erased erased erased
           erased
           erased
           erased
           erased
           (coe MAlonzo.Code.Function.d68 erased erased)
           (\ v5 -> MAlonzo.Code.Data.Product.d28))
      (coe du350 v1 v0
         (\ v4 -> coe v2 (coe MAlonzo.Code.Function.du68 v4))
         v3)
name827 = "Data.List.Any..absurdlambda"
d827 = erased