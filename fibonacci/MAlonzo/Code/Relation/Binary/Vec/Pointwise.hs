{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.Vec.Pointwise where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Category.Applicative.Indexed
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Plus
import qualified MAlonzo.Code.Data.Vec
import qualified MAlonzo.Code.Data.Vec.Properties
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Equivalence
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary
import qualified MAlonzo.Code.Relation.Nullary.Decidable
name22 = "Relation.Binary.Vec.Pointwise.Pointwise"
d22 a0 a1 a2 a3 a4 a5 a6 = ()

newtype T22 a0 = C46 a0
name44 = "Relation.Binary.Vec.Pointwise.Pointwise.app"
d44 v0
  = case coe v0 of
        C46 v1 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name56 = "Relation.Binary.Vec.Pointwise.Pointwise\8242"
d56 a0 a1 a2 a3 a4 a5 a6 = ()

data T56 a0 a1 a2 a3 a4 a5 a6 = C72
                              | C88 a0 a1 a2 a3 a4 a5 a6
name104 = "Relation.Binary.Vec.Pointwise.equivalent"
d104 v0 v1 v2 v3 v4 v5 v6 = du104 v5 v6
du104 v0 v1
  = coe MAlonzo.Code.Function.Equivalence.du56 erased erased
      (coe d122 erased erased erased erased erased erased erased erased
         v0
         v1)
      (coe d178 erased erased erased erased erased erased erased erased
         erased
         erased)
name122 = "Relation.Binary.Vec.Pointwise._.to"
d122 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du122 v8 v9 v10
du122 v0 v1 v2
  = case coe v0 of
        MAlonzo.Code.Data.Vec.C14 -> coe seq v1 (coe C72)
        MAlonzo.Code.Data.Vec.C22 v3 v4 v5 -> case coe v1 of
                                                  MAlonzo.Code.Data.Vec.C22 v6 v7 v8 -> coe C88 v3
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Vec.du696
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Fin.C8
                                                                                                v3)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Vec.C22
                                                                                                v3
                                                                                                v4
                                                                                                v5))
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Vec.du696
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Fin.C8
                                                                                                v3)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Vec.C22
                                                                                                v3
                                                                                                v7
                                                                                                v8))
                                                                                          v5
                                                                                          v8
                                                                                          (coe d44
                                                                                             v2
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Fin.C8
                                                                                                v3))
                                                                                          (coe du122
                                                                                             v5
                                                                                             v8
                                                                                             (coe
                                                                                                C46
                                                                                                (coe
                                                                                                   MAlonzo.Code.Function.d38
                                                                                                   erased
                                                                                                   erased
                                                                                                   erased
                                                                                                   erased
                                                                                                   erased
                                                                                                   erased
                                                                                                   (\ v9
                                                                                                      ->
                                                                                                      coe
                                                                                                        d44
                                                                                                        v2)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.Fin.C14
                                                                                                      v3))))
                                                  _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name136 = "Relation.Binary.Vec.Pointwise._.nil"
d136 v0 v1 v2 v3 v4 v5 v6 = du136
du136 = coe C46 erased
name148 = "Relation.Binary.Vec.Pointwise._.cons"
d148 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 = du148 v12 v13
du148 v0 v1
  = coe C46
      (coe d168 erased erased erased erased erased erased erased erased
         erased
         erased
         erased
         erased
         v0
         v1)
name168 = "Relation.Binary.Vec.Pointwise._._.helper"
d168 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du168 v12 v13 v14
du168 v0 v1 v2
  = case coe v2 of
        MAlonzo.Code.Data.Fin.C8 v3 -> coe v0
        MAlonzo.Code.Data.Fin.C14 v3 v4 -> coe d44 v1 v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name178 = "Relation.Binary.Vec.Pointwise._.from"
d178 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du178 v10
du178 v0
  = case coe v0 of
        C72 -> coe du136
        C88 v1 v2 v3 v4 v5 v6 v7 -> coe du148 v6 (coe du178 v7)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name202 = "Relation.Binary.Vec.Pointwise.head"
d202 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du202 v9
du202 v0
  = case coe v0 of
        C88 v1 v2 v3 v4 v5 v6 v7 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name226 = "Relation.Binary.Vec.Pointwise.tail"
d226 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du226 v9
du226 v0
  = case coe v0 of
        C88 v1 v2 v3 v4 v5 v6 v7 -> coe v7
        _ -> coe MAlonzo.RTE.mazUnreachableError
name240 = "Relation.Binary.Vec.Pointwise.refl"
d240 v0 v1 v2 v3 v4 v5 = du240 v4 v5
du240 v0 v1
  = coe C46 (\ v2 -> coe v0 (coe MAlonzo.Code.Data.Vec.du696 v2 v1))
name258 = "Relation.Binary.Vec.Pointwise.sym"
d258 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du258 v6 v7 v8 v9
du258 v0 v1 v2 v3
  = coe C46
      (\ v4 ->
         coe v0 (coe MAlonzo.Code.Data.Vec.du696 v4 v1)
           (coe MAlonzo.Code.Data.Vec.du696 v4 v2)
           (coe d44 v3 v4))
name282 = "Relation.Binary.Vec.Pointwise.trans"
d282 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du282 v8 v9 v10 v11 v12 v13
du282 v0 v1 v2 v3 v4 v5
  = coe C46
      (\ v6 ->
         coe v0 (coe MAlonzo.Code.Data.Vec.du696 v6 v1)
           (coe MAlonzo.Code.Data.Vec.du696 v6 v2)
           (coe MAlonzo.Code.Data.Vec.du696 v6 v3)
           (coe d44 v4 v6)
           (coe d44 v5 v6))
name300 = "Relation.Binary.Vec.Pointwise.isEquivalence"
d300 v0 v1 v2 v3 v4 = du300 v4
du300 v0
  = coe MAlonzo.Code.Relation.Binary.Core.C605
      (coe d240 erased erased erased erased
         (coe MAlonzo.Code.Relation.Binary.Core.d516 v0))
      (coe d258 erased erased erased erased erased erased
         (coe MAlonzo.Code.Relation.Binary.Core.d518 v0))
      (coe d282 erased erased erased erased erased erased erased erased
         (coe MAlonzo.Code.Relation.Binary.Core.d520 v0))
name314 = "Relation.Binary.Vec.Pointwise.decidable"
d314 v0 v1 v2 v3 v4 v5 v6 v7 = du314 v4 v6 v7
du314 v0 v1 v2
  = coe MAlonzo.Code.Relation.Nullary.Decidable.du80
      (coe MAlonzo.Code.Relation.Binary.Core.d518
         (coe MAlonzo.Code.Relation.Binary.d136
            MAlonzo.Code.Function.Equivalence.du218)
         erased
         erased
         (coe du104 v1 v2))
      (coe du330 v0 v1 v2)
name330 = "Relation.Binary.Vec.Pointwise._.decidable\8242"
d330 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du330 v4 v9 v10
du330 v0 v1 v2
  = case coe v1 of
        MAlonzo.Code.Data.Vec.C14 -> coe seq v2
                                       (coe MAlonzo.Code.Relation.Nullary.C22 (coe C72))
        MAlonzo.Code.Data.Vec.C22 v3 v4 v5 -> case coe v2 of
                                                  MAlonzo.Code.Data.Vec.C22 v6 v7 v8 -> let v9
                                                                                              = coe
                                                                                                  v0
                                                                                                  v4
                                                                                                  v7
                                                                                          in
                                                                                          case
                                                                                            coe v9
                                                                                            of
                                                                                              MAlonzo.Code.Relation.Nullary.C22
                                                                                                v10 -> let v11
                                                                                                             = coe
                                                                                                                 du330
                                                                                                                 v0
                                                                                                                 v5
                                                                                                                 v8
                                                                                                         in
                                                                                                         case
                                                                                                           coe
                                                                                                             v11
                                                                                                           of
                                                                                                             MAlonzo.Code.Relation.Nullary.C22
                                                                                                               v12 -> coe
                                                                                                                        MAlonzo.Code.Relation.Nullary.C22
                                                                                                                        (coe
                                                                                                                           C88
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v7
                                                                                                                           v5
                                                                                                                           v8
                                                                                                                           v10
                                                                                                                           v12)
                                                                                                             MAlonzo.Code.Relation.Nullary.C26
                                                                                                               v12 -> coe
                                                                                                                        MAlonzo.Code.Relation.Nullary.C26
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Function.d38
                                                                                                                           erased
                                                                                                                           erased
                                                                                                                           erased
                                                                                                                           erased
                                                                                                                           erased
                                                                                                                           erased
                                                                                                                           (\ v13
                                                                                                                              ->
                                                                                                                              v12)
                                                                                                                           (coe
                                                                                                                              d226
                                                                                                                              erased
                                                                                                                              erased
                                                                                                                              erased
                                                                                                                              erased
                                                                                                                              erased
                                                                                                                              erased
                                                                                                                              erased
                                                                                                                              erased
                                                                                                                              erased))
                                                                                                             _ -> coe
                                                                                                                    MAlonzo.RTE.mazUnreachableError
                                                                                              MAlonzo.Code.Relation.Nullary.C26
                                                                                                v10 -> coe
                                                                                                         MAlonzo.Code.Relation.Nullary.C26
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Function.d38
                                                                                                            erased
                                                                                                            erased
                                                                                                            erased
                                                                                                            erased
                                                                                                            erased
                                                                                                            erased
                                                                                                            (\ v11
                                                                                                               ->
                                                                                                               v10)
                                                                                                            (coe
                                                                                                               d202
                                                                                                               erased
                                                                                                               erased
                                                                                                               erased
                                                                                                               erased
                                                                                                               erased
                                                                                                               erased
                                                                                                               erased
                                                                                                               erased
                                                                                                               erased))
                                                                                              _ -> coe
                                                                                                     MAlonzo.RTE.mazUnreachableError
                                                  _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name337 = "Relation.Binary.Vec.Pointwise._..absurdlambda"
d337 = erased
name402 = "Relation.Binary.Vec.Pointwise.Pointwise-\8801"
d402 v0 v1 v2 v3 v4 = du402 v3 v4
du402 v0 v1
  = coe MAlonzo.Code.Function.Equivalence.du56 erased erased
      (coe MAlonzo.Code.Function.d38 erased erased erased erased erased
         erased
         erased
         (coe MAlonzo.Code.Function.Equality.d38
            (coe MAlonzo.Code.Function.Equivalence.d34 (coe du104 v0 v1))))
      (\ v2 ->
         coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du28
           (coe du240 erased v0))
name418 = "Relation.Binary.Vec.Pointwise._.to"
d418 = erased
name436 = "Relation.Binary.Vec.Pointwise.\8314\8729\8658\8729\8314"
d436 v0 v1 v2 v3 v4 v5 v6 = du436 v4 v5 v6
du436 v0 v1 v2
  = case coe v2 of
        MAlonzo.Code.Data.Plus.C28 v3 v4 v5 -> coe C46
                                                 (\ v6 ->
                                                    coe MAlonzo.Code.Data.Plus.C28
                                                      (coe MAlonzo.Code.Data.Vec.du696 v6 v0)
                                                      (coe MAlonzo.Code.Data.Vec.du696 v6 v1)
                                                      (coe d44 v5 v6))
        MAlonzo.Code.Data.Plus.C40 v3 v4 v5 v6 v7 -> coe C46
                                                       (\ v8 ->
                                                          coe MAlonzo.Code.Data.Plus.C40
                                                            (coe MAlonzo.Code.Data.Vec.du696 v8 v3)
                                                            (coe MAlonzo.Code.Data.Vec.du696 v8 v4)
                                                            (coe MAlonzo.Code.Data.Vec.du696 v8 v1)
                                                            (coe d44 (coe du436 v3 v4 v6) v8)
                                                            (coe d44 (coe du436 v4 v1 v7) v8))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name462 = "Relation.Binary.Vec.Pointwise.\8729\8314\8658\8314\8729"
d462 v0 v1 v2 v3 v4 v5 v6 = du462 v4 v5 v6
du462 v0 v1 v2
  = coe MAlonzo.Code.Function.d38 erased erased erased erased erased
      erased
      (\ v3 ->
         coe MAlonzo.Code.Data.Plus.d74 erased erased erased erased erased
           erased
           erased
           erased
           (\ v4 -> v4)
           (\ v4 v5 ->
              coe MAlonzo.Code.Function.Equality.d38
                (coe MAlonzo.Code.Function.Equivalence.d36 (coe du104 v4 v5)))
           v0
           v1)
      (coe MAlonzo.Code.Function.d38 erased erased erased erased erased
         erased
         (\ v3 ->
            coe d482 erased erased erased erased erased erased v2 erased erased
              erased)
         (coe MAlonzo.Code.Function.Equality.d38
            (coe MAlonzo.Code.Function.Equivalence.d34 (coe du104 v0 v1))))
name482 = "Relation.Binary.Vec.Pointwise._.helper"
d482 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du482 v6 v10
du482 v0 v1
  = case coe v1 of
        C72 -> coe MAlonzo.Code.Data.Plus.C28
                 (coe MAlonzo.Code.Data.Vec.C14)
                 (coe MAlonzo.Code.Data.Vec.C14)
                 (coe C72)
        C88 v2 v3 v4 v5 v6 v7 v8 -> coe MAlonzo.Code.Data.Plus.C40
                                      (coe MAlonzo.Code.Data.Vec.C22 v2 v3 v5)
                                      (coe MAlonzo.Code.Data.Vec.C22 v2 v4 v5)
                                      (coe MAlonzo.Code.Data.Vec.C22 v2 v4 v6)
                                      (coe MAlonzo.Code.Data.Plus.du74
                                         (\ v9 -> coe MAlonzo.Code.Data.Vec.C22 v2 v9 v5)
                                         (\ v9 v10 v11 ->
                                            coe C88 v2 v9 v10 v5 v5 v11 (coe du500 v0 v5))
                                         v3
                                         v4
                                         v7)
                                      (coe MAlonzo.Code.Data.Plus.du54
                                         (coe MAlonzo.Code.Data.Plus.du74
                                            (coe MAlonzo.Code.Data.Vec.C22 v2 v4)
                                            (\ v9 v10 -> coe C88 v2 v4 v4 v9 v10 (coe v0 v4))
                                            v5
                                            v6
                                            (coe du482 v0 v8)))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name500 = "Relation.Binary.Vec.Pointwise._._.xs\8764xs"
d500 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 = du500 v6 v9
du500 v0 v1
  = coe MAlonzo.Code.Function.Equality.d38
      (coe MAlonzo.Code.Function.Equivalence.d34 (coe du104 v1 v1))
      (coe du240 v0 v1)
name558 = "Relation.Binary.Vec.Pointwise.map"
d558 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du558 v5 v6 v7 v8
du558 v0 v1 v2 v3
  = coe C46
      (\ v4 ->
         coe v0 (coe MAlonzo.Code.Data.Vec.du696 v4 v1)
           (coe MAlonzo.Code.Data.Vec.du696 v4 v2)
           (coe d44 v3 v4))
name580 = "Relation.Binary.Vec.Pointwise.gmap"
d580 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du580 v7 v8 v9 v10
du580 v0 v1 v2 v3
  = coe C46
      (\ v4 ->
         coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du26
           (coe v0 (coe MAlonzo.Code.Data.Vec.du696 v4 v1)
              (coe MAlonzo.Code.Data.Vec.du696 v4 v2)
              (coe d44 v3 v4)))
name600 = "Relation.Binary.Vec.Pointwise.M.op-<$>"
d600 = erased