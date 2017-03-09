{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Colist where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Coinduction
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Category.Monad
import qualified MAlonzo.Code.Coinduction
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.BoundedVec.Inefficient
import qualified MAlonzo.Code.Data.Conat
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.NonEmpty
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Inverse
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.InducedPreorders
import qualified MAlonzo.Code.Relation.Binary.PartialOrderReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified MAlonzo.Code.Relation.Nullary
import qualified MAlonzo.Code.Relation.Nullary.Negation

type AgdaColist a b = [b] {- OMG hack :: -}
name10 = "Data.Colist.\172\172Monad._._<$_"
d10 = erased
name12 = "Data.Colist.\172\172Monad._._<$>_"
d12 = erased
name14 = "Data.Colist.\172\172Monad._._<=<_"
d14 = erased
name16 = "Data.Colist.\172\172Monad._._<\8859_"
d16 = erased
name18 = "Data.Colist.\172\172Monad._._=<<_"
d18 = erased
name20 = "Data.Colist.\172\172Monad._._>=>_"
d20 = erased
name22 = "Data.Colist.\172\172Monad._._>>_"
d22 = erased
name24 = "Data.Colist.\172\172Monad._._>>=_"
d24 = erased
name26 = "Data.Colist.\172\172Monad._._\8855_"
d26 = erased
name28 = "Data.Colist.\172\172Monad._._\8859_"
d28 = erased
name30 = "Data.Colist.\172\172Monad._._\8859>_"
d30 = erased
name32 = "Data.Colist.\172\172Monad._.join"
d32 = erased
name34 = "Data.Colist.\172\172Monad._.pure"
d34 = erased
name36 = "Data.Colist.\172\172Monad._.rawFunctor"
d36 v0 = du36
du36
  = coe MAlonzo.Code.Category.Monad.du70
      MAlonzo.Code.Relation.Nullary.Negation.du220
name38 = "Data.Colist.\172\172Monad._.rawIApplicative"
d38 v0 = du38
du38
  = coe MAlonzo.Code.Category.Monad.du72
      MAlonzo.Code.Relation.Nullary.Negation.du220
name40 = "Data.Colist.\172\172Monad._.return"
d40 = erased
name42 = "Data.Colist.\172\172Monad._.zipWith"
d42 = erased
name48 = "Data.Colist.Colist"
d48 a0 a1 = ()

check54 ::
        (forall xa. (forall xA. (MAlonzo.Code.Data.Colist.AgdaColist xa xA)))
check54 = []

check60 ::
        (forall xa. (forall xA. (xA -> ((MAlonzo.Code.Data.Colist.AgdaColist xa xA) -> (MAlonzo.Code.Data.Colist.AgdaColist xa xA)))))
check60 = (:)

cover48 :: MAlonzo.Code.Data.Colist.AgdaColist a1 a2 -> ()
cover48 x
  = case x of
        [] -> ()
        (:) _ _ -> ()
name54 = "Data.Colist.Colist.[]"

d54 ::
    (forall xa. (forall xA. (MAlonzo.Code.Data.Colist.AgdaColist xa xA)))
d54 = []
name60 = "Data.Colist.Colist._\8759_"

d60 ::
    (forall xa. (forall xA. (xA -> ((MAlonzo.Code.Data.Colist.AgdaColist xa xA) -> (MAlonzo.Code.Data.Colist.AgdaColist xa xA)))))
d60 = (:)
name70 = "Data.Colist.Any"
d70 a0 a1 a2 a3 a4 = ()

data T70 a0 a1 a2 = C86 a0 a1 a2
                  | C94 a0 a1 a2
name104 = "Data.Colist.All"
d104 a0 a1 a2 a3 a4 = ()

data T104 a0 a1 a2 a3 = C114
                      | C124 a0 a1 a2 a3
name130 = "Data.Colist.null"
d130 v0 v1 v2 = du130 v2
du130 v0
  = case coe v0 of
        [] -> coe True
        (:) v1 v2 -> coe False
        _ -> coe MAlonzo.RTE.mazUnreachableError
name136 = "Data.Colist.length"
d136 v0 v1 v2
  = case coe v2 of
        [] -> coe MAlonzo.Code.Data.Conat.C6
        (:) v3 v4 -> coe MAlonzo.Code.Data.Conat.C10 (coe du159 v0 v1 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name150 = "Data.Colist.map"
d150 v0 v1 v2 v3 v4 v5
  = case coe v5 of
        [] -> coe []
        (:) v6 v7 -> coe (:) (coe v4 v6) (coe du293 v0 v1 v2 v3 v4 v7)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name159 = "Data.Colist._.\9839-0"
d159 v0 v1 v2 v3 = du159 v0 v1 v3
du159 v0 v1 v2
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d136 v0 v1 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2))
name164 = "Data.Colist.fromList"
d164 v0 v1 v2
  = case coe v2 of
        [] -> coe []
        (:) v3 v4 -> coe (:) v3 (coe du427 v0 v1 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name176 = "Data.Colist.take"
d176 v0 v1 v2 v3 = du176 v2 v3
du176 v0 v1
  = case coe v0 of
        0 -> coe MAlonzo.Code.Data.BoundedVec.Inefficient.C18
               (0 :: Integer)
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   [] -> coe MAlonzo.Code.Data.BoundedVec.Inefficient.C18 v0
                   (:) v3 v4 -> coe MAlonzo.Code.Data.BoundedVec.Inefficient.C26 v2 v3
                                  (coe du176 v2 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v4))
                   _ -> coe MAlonzo.RTE.mazUnreachableError
name192 = "Data.Colist.replicate"
d192 v0 v1 v2 v3
  = case coe v2 of
        MAlonzo.Code.Data.Conat.C6 -> coe []
        MAlonzo.Code.Data.Conat.C10 v4 -> coe (:) v3 (coe d645 v0 v1 v4 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name204 = "Data.Colist.lookup"
d204 v0 v1 v2 v3 = du204 v2 v3
du204 v0 v1
  = case coe v1 of
        [] -> coe Nothing
        (:) v2 v3 -> case coe v0 of
                         0 -> coe Just v2
                         _ -> let v4
                                    = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                                        (1 :: Integer)
                                in coe du204 v4 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name222 = "Data.Colist._++_"
d222 v0 v1 v2 v3
  = case coe v2 of
        [] -> coe v3
        (:) v4 v5 -> coe (:) v4 (coe du881 v0 v1 v5 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name236 = "Data.Colist._\8910_"
d236 v0 v1 v2 v3
  = case coe v2 of
        [] -> coe v3
        (:) v4 v5 -> coe (:) v4 (coe du989 v0 v1 v5 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name250 = "Data.Colist.concat"
d250 v0 v1 v2
  = case coe v2 of
        [] -> coe []
        (:) v3 v4 -> case coe v3 of
                         MAlonzo.Code.Data.List.NonEmpty.C24 v5 v6 -> case coe v6 of
                                                                          [] -> coe (:) v5
                                                                                  (coe du1117 v0 v1
                                                                                     v4)
                                                                          (:) v7 v8 -> coe (:) v5
                                                                                         (coe du1177
                                                                                            v0
                                                                                            v1
                                                                                            v7
                                                                                            v8
                                                                                            v4)
                                                                          _ -> coe
                                                                                 MAlonzo.RTE.mazUnreachableError
                         _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name268 = "Data.Colist.[_]"
d268 v0 v1 v2 = du268 v2
du268 v0 = coe (:) v0 du1347
name288 = "Data.Colist.Any-map"
d288 v0 v1 v2 v3 v4 v5 v6 v7 = du288 v0 v1 v3 v4 v6 v7
du288 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Function.Inverse.C173
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du210
         (coe MAlonzo.Code.Relation.Binary.C85 erased erased
            (coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased))
         (coe d300 erased erased erased erased erased erased erased erased
            v5))
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du210
         (coe MAlonzo.Code.Relation.Binary.C85 erased erased
            (coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased))
         (coe d316 v0 v1 erased v2 v3 erased v4 erased v5))
      (coe MAlonzo.Code.Function.Inverse.C109 erased erased)
name293 = "Data.Colist._.\9839-1"
d293 v0 v1 v2 v3 v4 v5 v6 = du293 v0 v1 v2 v3 v4 v6
du293 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d150 v0 v1 v2 v3 v4
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v5))
name300 = "Data.Colist._.to"
d300 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du300 v8 v9
du300 v0 v1
  = case coe v0 of
        (:) v2 v3 -> case coe v1 of
                         C86 v4 v5 v6 -> coe C86 v2 v3 v6
                         C94 v4 v5 v6 -> coe C94 v2 v3
                                           (coe du300
                                              (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v3)
                                              v6)
                         _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name316 = "Data.Colist._.from"
d316 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du316 v0 v1 v3 v4 v6 v8 v9
du316 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
        (:) v7 v8 -> case coe v6 of
                         C86 v9 v10 v11 -> coe C86 (coe v4 v7) (coe du293 v0 v1 v2 v3 v4 v8)
                                             v11
                         C94 v9 v10 v11 -> coe C94 (coe v4 v7) (coe du293 v0 v1 v2 v3 v4 v8)
                                             (coe du316 v0 v1 v2 v3 v4
                                                (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v8)
                                                v11)
                         _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name334 = "Data.Colist._.from\8728to"
d334 = erased
name352 = "Data.Colist._.to\8728from"
d352 = erased
name380 = "Data.Colist.Any-\8910"
d380 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Function.Inverse.C173
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du210
         (coe MAlonzo.Code.Relation.Binary.C85 erased erased
            (coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased))
         (coe d392 erased erased erased erased v4 v5))
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du210
         (coe MAlonzo.Code.Relation.Binary.C85 erased erased
            (coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased))
         (coe d438 v0 v1 v2 v3 v4 v5))
      (coe MAlonzo.Code.Function.Inverse.C109 erased erased)
name392 = "Data.Colist._.to"
d392 v0 v1 v2 v3 v4 v5 v6 = du392 v4 v5 v6
du392 v0 v1 v2
  = case coe v0 of
        [] -> coe Right v2
        (:) v3 v4 -> case coe v2 of
                         C86 v5 v6 v7 -> coe Left (coe C86 v3 v4 v7)
                         C94 v5 v6 v7 -> coe MAlonzo.Code.Data.Sum.du74 (coe Right)
                                           (coe MAlonzo.Code.Function.d38 erased erased erased
                                              erased
                                              erased
                                              erased
                                              (\ v8 -> coe Left)
                                              (coe C94 v3 v4))
                                           (coe du392 v1
                                              (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v4)
                                              v7)
                         _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name412 = "Data.Colist._.from-left"
d412 v0 v1 v2 v3 v4 v5 v6 = du412 v0 v1 v2 v3 v5 v6
du412 v0 v1 v2 v3 v4 v5
  = case coe v5 of
        C86 v6 v7 v8 -> coe C86 v6 (coe du989 v0 v2 v7 v4) v8
        C94 v6 v7 v8 -> coe C94 v6 (coe du989 v0 v2 v7 v4)
                          (coe d418 v0 v1 v2 v3 v4
                             (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v7)
                             v8)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name418 = "Data.Colist._.from-right"
d418 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
        [] -> coe v6
        (:) v7 v8 -> coe C94 v7 (coe du989 v0 v2 v8 v5)
                       (coe du412 v0 v1 v2 v3
                          (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v8)
                          v6)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name427 = "Data.Colist._.\9839-2"
d427 v0 v1 v2 v3 = du427 v0 v1 v3
du427 v0 v1 v2
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 (coe d164 v0 v1 v2)
name438 = "Data.Colist._.from"
d438 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Data.Sum.d48 erased erased erased erased erased
      erased
      (coe d412 v0 v1 v2 v3 erased v5)
      (coe d418 v0 v1 v2 v3 v4 v5)
name448 = "Data.Colist._.from\8728to"
d448 = erased
name492 = "Data.Colist._.to\8728from-left"
d492 = erased
name500 = "Data.Colist._.to\8728from-right"
d500 = erased
name532 = "Data.Colist._.to\8728from"
d532 = erased
name542 = "Data.Colist._\8776_"
d542 a0 a1 a2 a3 = ()

data T542 a0 a1 a2 a3 = C552
                      | C562 a0 a1 a2 a3
name566 = "Data.Colist.setoid"
d566 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Relation.Binary.Core.C605 (coe d574 v0 v1)
         (coe d580 v0 v1)
         (coe d586 v0 v1))
name574 = "Data.Colist._.refl"
d574 v0 v1 v2
  = case coe v2 of
        [] -> coe C552
        (:) v3 v4 -> coe C562 v3 v4 v4 (coe du5789 v0 v1 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name580 = "Data.Colist._.sym"
d580 v0 v1 v2 v3 v4 = du580 v0 v1 v4
du580 v0 v1 v2
  = case coe v2 of
        C552 -> coe C552
        C562 v3 v4 v5 v6 -> coe C562 v3 v5 v4 (coe du5853 v0 v1 v4 v5 v6)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name586 = "Data.Colist._.trans"
d586 v0 v1 v2 v3 v4 v5 v6 = du586 v0 v1 v5 v6
du586 v0 v1 v2 v3
  = case coe v2 of
        C552 -> coe seq v3 (coe C552)
        C562 v4 v5 v6 v7 -> case coe v3 of
                                C562 v8 v9 v10 v11 -> coe C562 v4 v5 v10
                                                        (coe du6061 v0 v1 v6 v10 v5 v7 v11)
                                _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name602 = "Data.Colist.\8776-Reasoning.R._IsRelatedTo_"
d602 a0 a1 a2 a3 = ()
name604 = "Data.Colist.\8776-Reasoning.R._\8718"
d604 v0 v1
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe d566 v0 v1)
name606 = "Data.Colist.\8776-Reasoning.R._\8764\10216_\10217_"
d606 v0 v1
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40
      (coe d566 v0 v1)
name608 = "Data.Colist.\8776-Reasoning.R._\8776\10216_\10217_"
d608 v0 v1
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du42
      (coe d566 v0 v1)
name610 = "Data.Colist.\8776-Reasoning.R._\8776\10216\10217_"
d610 v0 v1 v2 = du610 v2
du610 v0 = coe v0
name612 = "Data.Colist.\8776-Reasoning.R.begin_"
d612 v0 v1 = du612
du612 = MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
name630 = "Data.Colist.map-cong"
d630 v0 v1 v2 v3 v4 v5 v6 v7 = du630 v0 v1 v2 v3 v4 v7
du630 v0 v1 v2 v3 v4 v5
  = case coe v5 of
        C552 -> coe C552
        C562 v6 v7 v8 v9 -> coe C562 (coe v4 v6)
                              (coe du293 v0 v1 v2 v3 v4 v7)
                              (coe du293 v0 v1 v2 v3 v4 v8)
                              (coe du6701 v0 v2 v7 v8 v1 v3 v4 v9)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name645 = "Data.Colist._.\9839-3"
d645 v0 v1 v2 v3
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d192 v0 v1 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2)
         v3)
name658 = "Data.Colist.Any-resp"
d658 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du658 v8 v9 v10
du658 v0 v1 v2
  = case coe v2 of
        C86 v3 v4 v5 -> case coe v1 of
                            C562 v6 v7 v8 v9 -> coe C86 v6 v8 (coe v0 v6 v5)
                            _ -> coe MAlonzo.RTE.mazUnreachableError
        C94 v3 v4 v5 -> case coe v1 of
                            C562 v6 v7 v8 v9 -> coe C94 v6 v8
                                                  (coe du658 v0
                                                     (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22
                                                        v9)
                                                     v5)
                            _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name694 = "Data.Colist.Any-cong"
d694 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du694 v0 v3 v6 v7 v8 v9
du694 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Function.Inverse.C173
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du210
         (coe MAlonzo.Code.Relation.Binary.C85 erased erased
            (coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased))
         (coe d658 erased erased erased erased erased erased erased erased
            (\ v6 ->
               coe MAlonzo.Code.Function.Equality.d38
                 (coe MAlonzo.Code.Function.Inverse.d78 (coe v4 v6)))
            v5))
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du210
         (coe MAlonzo.Code.Relation.Binary.C85 erased erased
            (coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased))
         (coe d658 erased erased erased erased erased erased erased erased
            (\ v6 ->
               coe MAlonzo.Code.Function.Equality.d38
                 (coe MAlonzo.Code.Function.Inverse.d80 (coe v4 v6)))
            (coe du708 v0 v1 v2 v3 v5)))
      (coe MAlonzo.Code.Function.Inverse.C109 erased erased)
name708 = "Data.Colist._._.sym"
d708 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du708 v0 v3
du708 v0 v1
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Relation.Binary.d136 (coe d566 v0 v1))
name732 = "Data.Colist._.resp\8728resp"
d732 = erased
name764 = "Data.Colist.index"
d764 v0 v1 v2 v3 v4 v5 = du764 v5
du764 v0
  = case coe v0 of
        C86 v1 v2 v3 -> 0 :: Integer
        C94 v1 v2 v3 -> coe ((Prelude.+) :: Integer -> Integer -> Integer)
                          (1 :: Integer)
                          (coe du764 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name782 = "Data.Colist.lookup-index"
d782 v0 v1 v2 v3 v4 v5 = du782 v5
du782 v0
  = case coe v0 of
        C86 v1 v2 v3 -> coe MAlonzo.Code.Data.Maybe.Base.C132 v1 erased
        C94 v1 v2 v3 -> coe du782 v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name812 = "Data.Colist.index-Any-resp"
d812 = erased
name840 = "Data.Colist.index-Any-\8910"
d840 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
        [] -> coe MAlonzo.Code.Data.Nat.Base.C68
        (:) v7 v8 -> case coe v6 of
                         C86 v9 v10 v11 -> coe MAlonzo.Code.Data.Nat.Base.C68
                         C94 v9 v10 v11 -> let v12
                                                 = coe MAlonzo.Code.Function.Equality.d38
                                                     (coe MAlonzo.Code.Function.Inverse.d78
                                                        (coe d380 v0 v1 v2 v3 v5
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Coinduction.d22
                                                              v8)))
                                                     v11
                                             in
                                             let v13
                                                   = coe d840 v0 v1 v2 v3 v5
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Coinduction.d22
                                                          v8)
                                                       v11
                                               in
                                               case coe v12 of
                                                   Left v14 -> coe MAlonzo.Code.Data.Nat.Base.C74
                                                                 (coe du764 v11)
                                                                 v13
                                                   Right v14 -> coe
                                                                  MAlonzo.Code.Data.Nat.Properties.du418
                                                                  v13
                                                   _ -> coe MAlonzo.RTE.mazUnreachableError
                         _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name881 = "Data.Colist._.\9839-4"
d881 v0 v1 v2 v3 v4 = du881 v0 v1 v3 v4
du881 v0 v1 v2 v3
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d222 v0 v1 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2)
         v3)
name890 = "Data.Colist._\8712_"
d890 = erased
name900 = "Data.Colist._\8838_"
d900 = erased
name912 = "Data.Colist._\8849_"
d912 a0 a1 a2 a3 = ()

data T912 a0 a1 a2 a3 = C920 a0
                      | C930 a0 a1 a2 a3
name944 = "Data.Colist.Any-\8712"
d944 v0 v1 v2 v3 v4 = du944
du944
  = coe MAlonzo.Code.Function.Inverse.C173
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du210
         (coe MAlonzo.Code.Relation.Binary.C85 erased erased
            (coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased))
         (coe d956 erased erased erased erased erased erased))
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du210
         (coe MAlonzo.Code.Relation.Binary.C85 erased erased
            (coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased))
         (\ v0 ->
            coe du966
              (coe MAlonzo.Code.Data.Product.d26
                 (coe MAlonzo.Code.Data.Product.d28 v0))
              (coe MAlonzo.Code.Data.Product.d28
                 (coe MAlonzo.Code.Data.Product.d28 v0))))
      (coe MAlonzo.Code.Function.Inverse.C109 erased erased)
name956 = "Data.Colist._.to"
d956 v0 v1 v2 v3 v4 v5 v6 = du956 v6
du956 v0
  = case coe v0 of
        C86 v1 v2 v3 -> coe MAlonzo.Code.Data.Product.C30 v1
                          (coe MAlonzo.Code.Data.Product.C30 (coe C86 v1 v2 erased) v3)
        C94 v1 v2 v3 -> coe MAlonzo.Code.Data.Product.du188
                          (coe MAlonzo.Code.Function.d68 erased erased)
                          (\ v4 ->
                             coe MAlonzo.Code.Data.Product.d188 erased erased erased erased
                               erased
                               erased
                               erased
                               erased
                               (coe C94 v1 v2)
                               (\ v5 -> coe MAlonzo.Code.Function.d68 erased erased))
                          (coe du956 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name966 = "Data.Colist._.from"
d966 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du966 v7 v8
du966 v0 v1
  = case coe v0 of
        C86 v2 v3 v4 -> coe C86 v2 v3 v1
        C94 v2 v3 v4 -> coe C94 v2 v3 (coe du966 v4 v1)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name982 = "Data.Colist._.to\8728from"
d982 = erased
name989 = "Data.Colist._.\9839-5"
d989 v0 v1 v2 v3 v4 = du989 v0 v1 v3 v4
du989 v0 v1 v2 v3
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d236 v0 v1 v3
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2))
name1000 = "Data.Colist._.from\8728to"
d1000 = erased
name1024 = "Data.Colist.\8849\8658\8838"
d1024 v0 v1 v2 v3 v4 v5 v6 = du1024 v4 v6
du1024 v0 v1
  = case coe v0 of
        C930 v2 v3 v4 v5 -> case coe v1 of
                                C86 v6 v7 v8 -> coe C86 v2 v4 v8
                                C94 v6 v7 v8 -> coe C94 v2 v4
                                                  (coe du1024
                                                     (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22
                                                        v5)
                                                     v8)
                                _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1038 = "Data.Colist.\8849-Poset"
d1038 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C235 erased erased erased
      (coe MAlonzo.Code.Relation.Binary.C217
         (coe MAlonzo.Code.Relation.Binary.C17
            (coe MAlonzo.Code.Relation.Binary.d136 (coe d566 v0 v1))
            (coe d1046 v0 v1)
            (coe d1052 v0 v1))
         (coe d1060 v0 v1))
name1046 = "Data.Colist._.reflexive"
d1046 v0 v1 v2 v3 v4 = du1046 v0 v1 v4
du1046 v0 v1 v2
  = case coe v2 of
        C552 -> coe C920 (coe [])
        C562 v3 v4 v5 v6 -> coe C930 v3 v4 v5 (coe du14601 v0 v1 v4 v5 v6)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1052 = "Data.Colist._.trans"
d1052 v0 v1 v2 v3 v4 v5 v6 = du1052 v0 v1 v4 v5 v6
du1052 v0 v1 v2 v3 v4
  = case coe v3 of
        C920 v5 -> coe C920 v2
        C930 v5 v6 v7 v8 -> case coe v4 of
                                C930 v9 v10 v11 v12 -> coe C930 v5 v6 v11
                                                         (coe du14823 v0 v1 v7 v11 v6 v8 v12)
                                _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1060 = "Data.Colist._.antisym"
d1060 v0 v1 v2 v3 v4 v5 = du1060 v0 v1 v4 v5
du1060 v0 v1 v2 v3
  = case coe v2 of
        C920 v4 -> case coe v3 of
                       C920 v5 -> coe C552
                       _ -> coe MAlonzo.RTE.mazUnreachableError
        C930 v4 v5 v6 v7 -> case coe v3 of
                                C930 v8 v9 v10 v11 -> coe C562 v4 v5 v6
                                                        (coe du15173 v0 v1 v6 v5 v7 v11)
                                _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1076 = "Data.Colist.\8849-Reasoning.R._IsRelatedTo_"
d1076 a0 a1 a2 a3 = ()
name1078 = "Data.Colist.\8849-Reasoning.R._\8718"
d1078 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.C56
      (coe MAlonzo.Code.Relation.Binary.d38
         (coe MAlonzo.Code.Relation.Binary.d268
            (coe MAlonzo.Code.Relation.Binary.d322 (coe d1038 v0 v1)))
         v2
         v2
         (coe MAlonzo.Code.Relation.Binary.Core.d516
            (coe MAlonzo.Code.Relation.Binary.d36
               (coe MAlonzo.Code.Relation.Binary.d268
                  (coe MAlonzo.Code.Relation.Binary.d322 (coe d1038 v0 v1))))
            v2))
name1080 = "Data.Colist.\8849-Reasoning.R._\8776\10216_\10217_"
d1080 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PartialOrderReasoning.du56
      (coe d1038 v0 v1)
name1082 = "Data.Colist.\8849-Reasoning.R._\8776\10216\10217_"
d1082 v0 v1 v2 = du1082 v2
du1082 v0 = coe v0
name1084 = "Data.Colist.\8849-Reasoning.R._\8764\10216_\10217_"
d1084 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PartialOrderReasoning.du60
      (coe d1038 v0 v1)
name1086 = "Data.Colist.\8849-Reasoning.R.begin_"
d1086 v0 v1 = du1086
du1086 = MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
name1096 = "Data.Colist.\8838-Preorder"
d1096 v0 v1
  = coe MAlonzo.Code.Relation.Binary.C67 erased erased
      (\ v2 v3 -> ())
      (coe MAlonzo.Code.Relation.Binary.C17
         (coe MAlonzo.Code.Relation.Binary.d136 (coe d566 v0 v1))
         (\ v2 v3 v4 v5 ->
            coe d1024 erased erased erased erased (coe d1124 v0 v1 v2 v3 v4)
              erased)
         (\ v2 v3 v4 v5 v6 v7 ->
            coe MAlonzo.Code.Function.d38 erased erased erased erased erased
              erased
              (\ v8 -> coe v6 v7)
              (coe v5 v7)))
name1117 = "Data.Colist._.\9839-6"
d1117 v0 v1 v2 v3 = du1117 v0 v1 v3
du1117 v0 v1 v2
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d250 v0 v1 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2))
name1124 = "Data.Colist._.\8849P.reflexive"
d1124 v0 v1
  = coe MAlonzo.Code.Relation.Binary.d38
      (coe MAlonzo.Code.Relation.Binary.d268
         (coe MAlonzo.Code.Relation.Binary.d322 (coe d1038 v0 v1)))
name1150 = "Data.Colist.\8838-Reasoning.R._IsRelatedTo_"
d1150 a0 a1 a2 a3 = ()
name1152 = "Data.Colist.\8838-Reasoning.R._\8718"
d1152 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.C56
      (coe MAlonzo.Code.Relation.Binary.d38
         (coe MAlonzo.Code.Relation.Binary.d92 (coe d1096 v0 v1))
         v2
         v2
         (coe MAlonzo.Code.Relation.Binary.Core.d516
            (coe MAlonzo.Code.Relation.Binary.d36
               (coe MAlonzo.Code.Relation.Binary.d92 (coe d1096 v0 v1)))
            v2))
name1154 = "Data.Colist.\8838-Reasoning.R._\8764\10216_\10217_"
d1154 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d72 erased
      erased
      erased
      (coe d1096 v0 v1)
name1156 = "Data.Colist.\8838-Reasoning.R._\8776\10216_\10217_"
d1156 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d84 erased
      erased
      erased
      (coe d1096 v0 v1)
name1158 = "Data.Colist.\8838-Reasoning.R._\8776\10216\10217_"
d1158 v0 v1 v2 = du1158 v2
du1158 v0 = coe v0
name1160 = "Data.Colist.\8838-Reasoning.R.begin_"
d1160 v0 v1 = du1160
du1160 = MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
name1177 = "Data.Colist._.\9839-7"
d1177 v0 v1 v2 v3 v4 v5 = du1177 v0 v1 v3 v4 v5
du1177 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d250 v0 v1
         (coe (:) (coe MAlonzo.Code.Data.List.NonEmpty.C24 v2 v3) v4))
name1178 = "Data.Colist.\8838-Reasoning._\8712\10216_\10217_"
d1178 v0 v1 v2 v3 v4 v5 v6 = du1178 v2 v5 v6
du1178 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62 v2 v0 v1
name1196 = "Data.Colist.take-\8849"
d1196 v0 v1 v2 v3
  = case coe v2 of
        0 -> coe C920 v3
        _ -> let v4
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v2
                       (1 :: Integer)
               in
               case coe v3 of
                   [] -> coe C920 (coe [])
                   (:) v5 v6 -> coe C930 v5
                                  (coe du427 v0 v1
                                     (coe MAlonzo.Code.Data.BoundedVec.Inefficient.du58
                                        (coe du176 v4
                                           (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v6))))
                                  v6
                                  (coe du15859 v0 v1 v4 v6)
                   _ -> coe MAlonzo.RTE.mazUnreachableError
name1212 = "Data.Colist.Finite"
d1212 a0 a1 a2 = ()

data T1212 a0 a1 a2 = C1218
                    | C1226 a0 a1 a2
name1232 = "Data.Colist.Infinite"
d1232 a0 a1 a2 = ()

data T1232 a0 a1 a2 = C1244 a0 a1 a2
name1252 = "Data.Colist.not-finite-is-infinite"
d1252 v0 v1 v2 v3 = du1252 v0 v1 v2
du1252 v0 v1 v2
  = case coe v2 of
        (:) v3 v4 -> coe C1244 v3 v4 (coe du16063 v0 v1 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1274 = "Data.Colist.finite-or-infinite"
d1274 = erased
name1282 = "Data.Colist._.helper"
d1282 v0 v1 v2 v3
  = case coe v3 of
        MAlonzo.Code.Relation.Nullary.C22 v4 -> coe Left v4
        MAlonzo.Code.Relation.Nullary.C26 v4 -> coe
                                                  MAlonzo.Code.Function.du158
                                                  (coe Right)
                                                  (coe du1252 v0 v1 v2)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1294 = "Data.Colist.not-finite-and-infinite"
d1294 = erased
name1347 = "Data.Colist._.\9839-8"
d1347 v0 v1 v2 = du1347
du1347 = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 (coe [])
name5789 = "Data.Colist._._.\9839-23"
d5789 v0 v1 v2 v3 = du5789 v0 v1 v3
du5789 v0 v1 v2
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d574 v0 v1 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2))
name5853 = "Data.Colist._._.\9839-25"
d5853 v0 v1 v2 v3 v4 v5 = du5853 v0 v1 v3 v4 v5
du5853 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe du580 v0 v1
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v4))
name6061 = "Data.Colist._._.\9839-27"
d6061 v0 v1 v2 v3 v4 v5 v6 v7 = du6061 v0 v1 v3 v4 v5 v6 v7
du6061 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe du586 v0 v1 (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v5)
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v6))
name6701 = "Data.Colist._.\9839-29"
d6701 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du6701 v0 v1 v3 v4 v5 v6 v7 v8
du6701 v0 v1 v2 v3 v4 v5 v6 v7
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe du630 v0 v4 v1 v5 v6
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v7))
name14601 = "Data.Colist._._.\9839-46"
d14601 v0 v1 v2 v3 v4 v5 = du14601 v0 v1 v3 v4 v5
du14601 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe du1046 v0 v1
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v4))
name14823 = "Data.Colist._._.\9839-48"
d14823 v0 v1 v2 v3 v4 v5 v6 v7 = du14823 v0 v1 v3 v4 v5 v6 v7
du14823 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe du1052 v0 v1
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v3)
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v5)
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v6))
name15173 = "Data.Colist._._.\9839-50"
d15173 v0 v1 v2 v3 v4 v5 v6 = du15173 v0 v1 v2 v4 v5 v6
du15173 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe du1060 v0 v1
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v4)
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v5))
name15859 = "Data.Colist._.\9839-52"
d15859 v0 v1 v2 v3 v4 = du15859 v0 v1 v2 v4
du15859 v0 v1 v2 v3
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe d1196 v0 v1 v2
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v3))
name16063 = "Data.Colist._.\9839-54"
d16063 v0 v1 v2 v3 v4 = du16063 v0 v1 v3
du16063 v0 v1 v2
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe du1252 v0 v1
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2))