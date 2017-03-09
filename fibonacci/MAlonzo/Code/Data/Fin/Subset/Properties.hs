{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Fin.Subset.Properties where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.Properties.BooleanAlgebra
import qualified MAlonzo.Code.Data.Bool.Properties
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.Fin.Subset
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Data.Vec
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Equivalence
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
name16 = "Data.Fin.Subset.Properties.drop-there"
d16 v0 v1 v2 v3 v4 = du16 v4
du16 v0
  = case coe v0 of
        MAlonzo.Code.Data.Vec.C88 v1 v2 v3 v4 v5 v6 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name30 = "Data.Fin.Subset.Properties.drop-\8759-\8838"
d30 v0 v1 v2 v3 v4 v5 v6 v7 = du30 v0 v1 v3 v5 v6 v7
du30 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Function.du158
      (coe d16 erased erased erased erased)
      (coe v3 (coe MAlonzo.Code.Data.Fin.C14 v0 v4)
         (coe MAlonzo.Code.Data.Vec.C88 v0 v4 (coe True) v1 v2 v5))
name42 = "Data.Fin.Subset.Properties.drop-\8759-Empty"
d42 = erased
name54 = "Data.Fin.Subset.Properties.\8713\8869"
d54 = erased
name62 = "Data.Fin.Subset.Properties.\8869\8838"
d62 v0 v1 v2 v3 = du62
du62 = MAlonzo.RTE.mazUnreachableError
name76 = "Data.Fin.Subset.Properties.Empty-unique"
d76 = erased
name98 = "Data.Fin.Subset.Properties.\8712\8868"
d98 v0 v1 = du98 v1
du98 v0
  = case coe v0 of
        MAlonzo.Code.Data.Fin.C8 v1 -> coe MAlonzo.Code.Data.Vec.C74 v1
                                         (coe MAlonzo.Code.Algebra.d1418
                                            MAlonzo.Code.Data.Bool.Properties.d372)
                                         (coe MAlonzo.Code.Data.Vec.du166 v1
                                            (coe MAlonzo.Code.Algebra.d1418
                                               MAlonzo.Code.Data.Bool.Properties.d372))
        MAlonzo.Code.Data.Fin.C14 v1 v2 -> coe MAlonzo.Code.Data.Vec.C88 v1
                                             v2
                                             (coe True)
                                             (coe MAlonzo.Code.Algebra.d1418
                                                MAlonzo.Code.Data.Bool.Properties.d372)
                                             (coe MAlonzo.Code.Data.Fin.Subset.d104 v1)
                                             (coe du98 v2)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name106 = "Data.Fin.Subset.Properties.\8838\8868"
d106 v0 v1 v2 = du106 v2
du106 v0
  = coe MAlonzo.Code.Function.d80 erased erased erased erased
      (coe du98 v0)
name114
  = "Data.Fin.Subset.Properties.x\8712\8261y\8262\8660x\8801y"
d114 v0 v1 v2 = du114 v1
du114 v0
  = coe MAlonzo.Code.Function.Equivalence.du56 erased erased erased
      (\ v1 ->
         coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du28
           (coe du148 v0))
name130 = "Data.Fin.Subset.Properties._.to"
d130 = erased
name148 = "Data.Fin.Subset.Properties._.x\8712\8261x\8262"
d148 v0 v1 v2 v3 v4 = du148 v4
du148 v0
  = case coe v0 of
        MAlonzo.Code.Data.Fin.C8 v1 -> coe MAlonzo.Code.Data.Vec.C74 v1
                                         (coe True)
                                         (coe MAlonzo.Code.Data.Fin.Subset.d106 v1)
        MAlonzo.Code.Data.Fin.C14 v1 v2 -> coe MAlonzo.Code.Data.Vec.C88 v1
                                             v2
                                             (coe True)
                                             (coe False)
                                             (coe MAlonzo.Code.Data.Fin.Subset.du110 v2)
                                             (coe du148 v2)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name164 = "Data.Fin.Subset.Properties.\8746\8660\8846"
d164 v0 v1 v2 v3 = du164 v1 v2 v3
du164 v0 v1 v2
  = coe MAlonzo.Code.Function.Equivalence.du56 erased erased
      (coe d178 erased erased erased erased erased v0 v1 erased)
      (coe d242 erased erased erased erased erased v0 v1 v2)
name178 = "Data.Fin.Subset.Properties._.to"
d178 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du178 v5 v6 v8
du178 v0 v1 v2
  = case coe v0 of
        MAlonzo.Code.Data.Vec.C22 v3 v4 v5 -> let v6
                                                    = case coe v1 of
                                                          MAlonzo.Code.Data.Vec.C22 v6 v7 v8 -> case
                                                                                                  coe
                                                                                                    v2
                                                                                                  of
                                                                                                    MAlonzo.Code.Data.Vec.C88
                                                                                                      v9
                                                                                                      v10
                                                                                                      v11
                                                                                                      v12
                                                                                                      v13
                                                                                                      v14 -> coe
                                                                                                               MAlonzo.Code.Data.Sum.du92
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.Vec.C88
                                                                                                                  v3
                                                                                                                  v10
                                                                                                                  (coe
                                                                                                                     True)
                                                                                                                  v4
                                                                                                                  v5)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.Vec.C88
                                                                                                                  v3
                                                                                                                  v10
                                                                                                                  (coe
                                                                                                                     True)
                                                                                                                  v7
                                                                                                                  v8)
                                                                                                               (coe
                                                                                                                  du178
                                                                                                                  v5
                                                                                                                  v8
                                                                                                                  v14)
                                                                                                    _ -> coe
                                                                                                           MAlonzo.RTE.mazUnreachableError
                                                          _ -> coe MAlonzo.RTE.mazUnreachableError
                                                in
                                                case coe v4 of
                                                    False -> case coe v1 of
                                                                 MAlonzo.Code.Data.Vec.C22 v7 v8
                                                                   v9 -> case coe v8 of
                                                                             True -> case coe v2 of
                                                                                         MAlonzo.Code.Data.Vec.C74
                                                                                           v10 v11
                                                                                           v12 -> coe
                                                                                                    Right
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.Vec.C74
                                                                                                       v3
                                                                                                       (coe
                                                                                                          True)
                                                                                                       v9)
                                                                                         _ -> coe v6
                                                                             _ -> coe v6
                                                                 _ -> coe v6
                                                    True -> case coe v1 of
                                                                MAlonzo.Code.Data.Vec.C22 v7 v8
                                                                  v9 -> case coe v2 of
                                                                            MAlonzo.Code.Data.Vec.C74
                                                                              v10 v11 v12 -> coe
                                                                                               Left
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C74
                                                                                                  v3
                                                                                                  (coe
                                                                                                     True)
                                                                                                  v5)
                                                                            _ -> coe v6
                                                                _ -> coe v6
                                                    _ -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name206 = "Data.Fin.Subset.Properties._.\8838\8746\737"
d206 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du206 v6 v8
du206 v0 v1
  = case coe v0 of
        MAlonzo.Code.Data.Vec.C22 v2 v3 v4 -> case coe v1 of
                                                  MAlonzo.Code.Data.Vec.C74 v5 v6 v7 -> coe
                                                                                          MAlonzo.Code.Data.Vec.C74
                                                                                          v2
                                                                                          (coe
                                                                                             MAlonzo.Code.Algebra.d1412
                                                                                             MAlonzo.Code.Data.Bool.Properties.d372
                                                                                             (coe
                                                                                                True)
                                                                                             v3)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Vec.du150
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Vec.du150
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.Vec.du166
                                                                                                   v2
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Algebra.d1412
                                                                                                      MAlonzo.Code.Data.Bool.Properties.d372))
                                                                                                v7)
                                                                                             v4)
                                                  MAlonzo.Code.Data.Vec.C88 v5 v6 v7 v8 v9
                                                    v10 -> coe MAlonzo.Code.Data.Vec.C88 v2 v6
                                                             (coe True)
                                                             (coe MAlonzo.Code.Algebra.d1412
                                                                MAlonzo.Code.Data.Bool.Properties.d372
                                                                v8
                                                                v3)
                                                             (coe MAlonzo.Code.Data.Fin.Subset.d52
                                                                v2
                                                                v9
                                                                v4)
                                                             (coe du206 v4 v10)
                                                  _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name224 = "Data.Fin.Subset.Properties._.\8838\8746\691"
d224 v0 v1 v2 v3 v4 v5 v6 = du224 v5
du224 v0 = coe d206 erased erased erased erased erased erased v0
name242 = "Data.Fin.Subset.Properties._.from"
d242 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du242 v5 v6 v7 v8
du242 v0 v1 v2 v3
  = case coe v3 of
        Left v4 -> coe du206 v1 v4
        Right v4 -> coe du224 v0 v2 v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name260 = "Data.Fin.Subset.Properties.NaturalPoset.BA.poset"
d260 v0
  = coe MAlonzo.Code.Algebra.Properties.BooleanAlgebra.du74
      (coe MAlonzo.Code.Data.Fin.Subset.d42 v0)
name330 = "Data.Fin.Subset.Properties.NaturalPoset.Po._\8776_"
d330 = erased
name332 = "Data.Fin.Subset.Properties.NaturalPoset.Po._\8804_"
d332 = erased
name334 = "Data.Fin.Subset.Properties.NaturalPoset.Po.Carrier"
d334 = erased
name336 = "Data.Fin.Subset.Properties.NaturalPoset.Po.antisym"
d336 = erased
name338
  = "Data.Fin.Subset.Properties.NaturalPoset.Po.isEquivalence"
d338 v0
  = coe MAlonzo.Code.Relation.Binary.d36
      (coe MAlonzo.Code.Relation.Binary.d268
         (coe MAlonzo.Code.Relation.Binary.d322 (coe d260 v0)))
name340
  = "Data.Fin.Subset.Properties.NaturalPoset.Po.isPartialOrder"
d340 v0 = coe MAlonzo.Code.Relation.Binary.d322 (coe d260 v0)
name342 = "Data.Fin.Subset.Properties.NaturalPoset.Po.isPreorder"
d342 v0
  = coe MAlonzo.Code.Relation.Binary.d268
      (coe MAlonzo.Code.Relation.Binary.d322 (coe d260 v0))
name344 = "Data.Fin.Subset.Properties.NaturalPoset.Po.preorder"
d344 v0
  = coe MAlonzo.Code.Relation.Binary.C67 erased erased erased
      (coe MAlonzo.Code.Relation.Binary.d268
         (coe MAlonzo.Code.Relation.Binary.d322 (coe d260 v0)))
name346 = "Data.Fin.Subset.Properties.NaturalPoset.Po.refl"
d346 = erased
name348 = "Data.Fin.Subset.Properties.NaturalPoset.Po.reflexive"
d348 = erased
name350 = "Data.Fin.Subset.Properties.NaturalPoset.Po.trans"
d350 = erased
name352
  = "Data.Fin.Subset.Properties.NaturalPoset.Po.\8764-resp-\8776"
d352 v0 = coe MAlonzo.Code.Relation.Binary.du338 (coe d260 v0)
name356 = "Data.Fin.Subset.Properties.NaturalPoset.Po.Eq.refl"
d356 = erased
name358 = "Data.Fin.Subset.Properties.NaturalPoset.Po.Eq.reflexive"
d358 = erased
name360 = "Data.Fin.Subset.Properties.NaturalPoset.Po.Eq.sym"
d360 = erased
name362 = "Data.Fin.Subset.Properties.NaturalPoset.Po.Eq.trans"
d362 = erased
name370
  = "Data.Fin.Subset.Properties.NaturalPoset.orders-equivalent"
d370 v0 v1 v2 = du370 v1 v2
du370 v0 v1
  = coe MAlonzo.Code.Function.Equivalence.du56 erased erased erased
      (coe d414 erased erased erased erased v0 v1)
name382 = "Data.Fin.Subset.Properties.NaturalPoset._.to"
d382 = erased
name414 = "Data.Fin.Subset.Properties.NaturalPoset._.from"
d414 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du414 v4 v5 v8
du414 v0 v1 v2
  = case coe v0 of
        MAlonzo.Code.Data.Vec.C14 -> coe seq v1 v2
        MAlonzo.Code.Data.Vec.C22 v3 v4 v5 -> case coe v1 of
                                                  MAlonzo.Code.Data.Vec.C22 v6 v7 v8 -> case coe v2
                                                                                          of
                                                                                            MAlonzo.Code.Data.Vec.C74
                                                                                              v9 v10
                                                                                              v11 -> coe
                                                                                                       MAlonzo.Code.Data.Vec.C74
                                                                                                       v3
                                                                                                       v7
                                                                                                       v8
                                                                                            MAlonzo.Code.Data.Vec.C88
                                                                                              v9 v10
                                                                                              v11
                                                                                              v12
                                                                                              v13
                                                                                              v14 -> coe
                                                                                                       MAlonzo.Code.Data.Vec.C88
                                                                                                       v3
                                                                                                       v10
                                                                                                       (coe
                                                                                                          True)
                                                                                                       v7
                                                                                                       v8
                                                                                                       (coe
                                                                                                          du414
                                                                                                          v5
                                                                                                          v8
                                                                                                          v14)
                                                                                            _ -> coe
                                                                                                   MAlonzo.RTE.mazUnreachableError
                                                  _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name434 = "Data.Fin.Subset.Properties.poset"
d434 v0 = du434
du434
  = coe MAlonzo.Code.Relation.Binary.C235 erased erased erased
      (coe MAlonzo.Code.Relation.Binary.C217
         (coe MAlonzo.Code.Relation.Binary.C17
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
            (\ v0 v1 v2 ->
               coe MAlonzo.Code.Function.Equality.d38 (coe du448 v0 v1) erased)
            (\ v0 v1 v2 v3 v4 ->
               coe MAlonzo.Code.Function.Equality.d38 (coe du448 v0 v2) erased))
         erased)
name448 = "Data.Fin.Subset.Properties._.E.from"
d448 v0 v1 v2 = du448 v1 v2
du448 v0 v1
  = coe MAlonzo.Code.Function.Equivalence.d36 (coe du370 v0 v1)
name450 = "Data.Fin.Subset.Properties._.E.to"
d450 v0 v1 v2 = du450 v1 v2
du450 v0 v1
  = coe MAlonzo.Code.Function.Equivalence.d34 (coe du370 v0 v1)