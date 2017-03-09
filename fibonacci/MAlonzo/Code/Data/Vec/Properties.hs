{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Vec.Properties where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Category.Applicative.Indexed
import qualified MAlonzo.Code.Category.Monad
import qualified MAlonzo.Code.Category.Monad.Identity
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.List.Any
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Vec
import qualified MAlonzo.Code.Data.Vec.Equality
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Inverse
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.HeterogeneousEquality
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
name42 = "Data.Vec.Properties.UsingVectorEquality._._\8776_"
d42 a0 a1 a2 a3 a4 a5 a6 = ()
name48 = "Data.Vec.Properties.UsingVectorEquality._.refl"
d48 v0 v1 v2 = du48 v2
du48 v0 = coe MAlonzo.Code.Data.Vec.Equality.d78 erased erased v0
name68 = "Data.Vec.Properties.UsingVectorEquality.replicate-lemma"
d68 v0 v1 v2 v3 v4 v5 v6 = du68 v2 v3 v4 v5 v6
du68 v0 v1 v2 v3 v4
  = case coe v2 of
        0 -> coe du48 v0
               (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                  v1)
               (coe MAlonzo.Code.Data.Vec.C22 v1 v3 v4)
        _ -> let v5
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v2
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Data.Vec.Equality.C60 v3
                 (coe ((Prelude.+) :: Integer -> Integer -> Integer) v1 v2)
                 (coe MAlonzo.Code.Data.Vec.du130
                    (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                       v1)
                    (coe MAlonzo.Code.Data.Vec.du166 v5 v3)
                    (coe MAlonzo.Code.Data.Vec.C22 v1 v3 v4))
                 v3
                 (coe ((Prelude.+) :: Integer -> Integer -> Integer) v1 v2)
                 (coe MAlonzo.Code.Data.Vec.du130 v1
                    (coe MAlonzo.Code.Data.Vec.du166 v2 v3)
                    v4)
                 (coe MAlonzo.Code.Relation.Binary.Core.d516
                    (coe MAlonzo.Code.Relation.Binary.d136 v0)
                    v3)
                 (coe du68 v0 v1 v5 v3 v4)
name84 = "Data.Vec.Properties.UsingVectorEquality.xs++[]=xs"
d84 v0 v1 v2 v3 v4 = du84 v2 v4
du84 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.Vec.C14 -> coe MAlonzo.Code.Data.Vec.Equality.C42
        MAlonzo.Code.Data.Vec.C22 v2 v3 v4 -> coe
                                                MAlonzo.Code.Data.Vec.Equality.C60
                                                v3
                                                v2
                                                (coe MAlonzo.Code.Data.Vec.du130 (0 :: Integer) v4
                                                   (coe MAlonzo.Code.Data.Vec.C14))
                                                v3
                                                v2
                                                v4
                                                (coe MAlonzo.Code.Relation.Binary.Core.d516
                                                   (coe MAlonzo.Code.Relation.Binary.d136 v0)
                                                   v3)
                                                (coe du84 v0 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name104 = "Data.Vec.Properties.UsingVectorEquality.map-++-commute"
d104 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du104 v2 v5 v7 v8
du104 v0 v1 v2 v3
  = case coe v3 of
        MAlonzo.Code.Data.Vec.C14 -> coe
                                       (\ v4 ->
                                          coe du48 v0 v1
                                            (coe MAlonzo.Code.Data.Vec.du192 v1 v2
                                               (coe MAlonzo.Code.Data.Vec.du130 v1
                                                  (coe MAlonzo.Code.Data.Vec.C14)
                                                  v4)))
        MAlonzo.Code.Data.Vec.C22 v4 v5 v6 -> coe
                                                (\ v7 ->
                                                   coe MAlonzo.Code.Data.Vec.Equality.C60
                                                     (coe v2 v5)
                                                     (coe
                                                        ((Prelude.+) :: Integer -> Integer -> Integer)
                                                        v1
                                                        v4)
                                                     (coe MAlonzo.Code.Data.Vec.du192
                                                        (coe
                                                           ((Prelude.+) :: Integer -> Integer -> Integer)
                                                           v1
                                                           v4)
                                                        v2
                                                        (coe MAlonzo.Code.Data.Vec.du130 v1 v6 v7))
                                                     (coe v2 v5)
                                                     (coe
                                                        ((Prelude.+) :: Integer -> Integer -> Integer)
                                                        v1
                                                        v4)
                                                     (coe MAlonzo.Code.Data.Vec.du130 v1
                                                        (coe MAlonzo.Code.Data.Vec.du192 v4 v2 v6)
                                                        (coe MAlonzo.Code.Data.Vec.du192 v1 v2 v7))
                                                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                                                        (coe MAlonzo.Code.Relation.Binary.d136 v0)
                                                        (coe v2 v5))
                                                     (coe du104 v0 v1 v2 v6 v7))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name128 = "Data.Vec.Properties.\8759-injective"
d128 v0 v1 v2 v3 v4 v5 v6 v7 = du128
du128 = coe MAlonzo.Code.Data.Product.C30 erased erased
name136 = "Data.Vec.Properties.lookup-morphism"
d136 v0 v1 v2 = du136 v2
du136 v0
  = coe MAlonzo.Code.Category.Applicative.Indexed.C177
      (\ v1 v2 v3 ->
         coe MAlonzo.Code.Data.Vec.d696 erased erased erased v0)
      erased
      erased
name152 = "Data.Vec.Properties._.lookup-replicate"
d152 = erased
name174 = "Data.Vec.Properties._.lookup-\8859"
d174 = erased
name204 = "Data.Vec.Properties.lookup\8728tabulate"
d204 = erased
name220 = "Data.Vec.Properties.tabulate\8728lookup"
d220 = erased
name230 = "Data.Vec.Properties.lookup-allFin"
d230 = erased
name248 = "Data.Vec.Properties.lookup-++-<"
d248 = erased
name286 = "Data.Vec.Properties.lookup-++-\8805"
d286 = erased
name324 = "Data.Vec.Properties.lookup-++-inject+"
d324 = erased
name356 = "Data.Vec.Properties.lookup-++-+\8242"
d356 = erased
name386 = "Data.Vec.Properties.lookup\8728update"
d386 = erased
name412 = "Data.Vec.Properties.lookup\8728update\8242"
d412 = erased
name466 = "Data.Vec.Properties.map-cong"
d466 = erased
name482 = "Data.Vec.Properties.map-id"
d482 = erased
name506 = "Data.Vec.Properties.map-\8728"
d506 = erased
name534 = "Data.Vec.Properties.tabulate-\8728"
d534 = erased
name554 = "Data.Vec.Properties.tabulate-allFin"
d554 = erased
name560 = "Data.Vec.Properties.allFin-map"
d560 = erased
name574 = "Data.Vec.Properties.map-lookup-allFin"
d574 = erased
name600 = "Data.Vec.Properties.\8712-tabulate"
d600 v0 v1 v2 v3 v4 = du600 v3 v4
du600 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.Fin.C8 v2 -> coe MAlonzo.Code.Data.Vec.C42 v2
                                         (coe v0 (coe MAlonzo.Code.Data.Fin.C8 v2))
                                         (coe MAlonzo.Code.Data.Vec.du714 v2
                                            (coe MAlonzo.Code.Function.d38 erased erased erased
                                               erased
                                               erased
                                               erased
                                               (\ v3 -> v0)
                                               (coe MAlonzo.Code.Data.Fin.C14 v2)))
        MAlonzo.Code.Data.Fin.C14 v2 v3 -> coe MAlonzo.Code.Data.Vec.C54 v2
                                             (coe MAlonzo.Code.Function.du38 (\ v4 -> v0)
                                                (coe MAlonzo.Code.Data.Fin.C14 v2)
                                                v3)
                                             (coe v0 (coe MAlonzo.Code.Data.Fin.C8 v2))
                                             (coe MAlonzo.Code.Data.Vec.du714 v2
                                                (coe MAlonzo.Code.Function.d38 erased erased erased
                                                   erased
                                                   erased
                                                   erased
                                                   (\ v4 -> v0)
                                                   (coe MAlonzo.Code.Data.Fin.C14 v2)))
                                             (coe du600
                                                (coe MAlonzo.Code.Function.d38 erased erased erased
                                                   erased
                                                   erased
                                                   erased
                                                   (\ v4 -> v0)
                                                   (coe MAlonzo.Code.Data.Fin.C14 v2))
                                                v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name612 = "Data.Vec.Properties.\8712-allFin"
d612 v0 = du612
du612
  = coe d600 erased erased erased
      (coe MAlonzo.Code.Function.d68 erased erased)
name622 = "Data.Vec.Properties.sum-++-commute"
d622 = erased
name662 = "Data.Vec.Properties._._.assoc"
d662 = erased
name766 = "Data.Vec.Properties.foldr-cong"
d766 = erased
name814 = "Data.Vec.Properties.foldl-cong"
d814 = erased
name852 = "Data.Vec.Properties.foldr-universal"
d852 = erased
name916 = "Data.Vec.Properties.foldr-fusion"
d916 = erased
name940 = "Data.Vec.Properties.idIsFold"
d940 = erased
name956 = "Data.Vec.Properties.\8712\8658List-\8712"
d956 v0 v1 v2 v3 v4 v5 = du956 v5
du956 v0
  = case coe v0 of
        MAlonzo.Code.Data.Vec.C42 v1 v2 v3 -> coe
                                                MAlonzo.Code.Data.List.Any.C30
                                                v2
                                                (coe MAlonzo.Code.Data.Vec.du530 v3)
                                                erased
        MAlonzo.Code.Data.Vec.C54 v1 v2 v3 v4 v5 -> coe
                                                      MAlonzo.Code.Data.List.Any.C38
                                                      v3
                                                      (coe MAlonzo.Code.Data.Vec.du530 v4)
                                                      (coe du956 v5)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name968 = "Data.Vec.Properties.List-\8712\8658\8712"
d968 v0 v1 v2 v3 v4 = du968 v2 v4
du968 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.List.Any.C30 v2 v3 v4 -> coe
                                                     MAlonzo.Code.Data.Vec.C42
                                                     (coe MAlonzo.Code.Data.List.Base.du144
                                                        (\ v5 v6 ->
                                                           coe
                                                             ((Prelude.+) :: Integer -> Integer -> Integer)
                                                             (1 :: Integer)
                                                             v6)
                                                        (0 :: Integer)
                                                        v3)
                                                     v2
                                                     (coe MAlonzo.Code.Data.Vec.du542 v3)
        MAlonzo.Code.Data.List.Any.C38 v2 v3 v4 -> coe
                                                     MAlonzo.Code.Data.Vec.C54
                                                     (coe MAlonzo.Code.Data.List.Base.du226 v3)
                                                     v0
                                                     v2
                                                     (coe MAlonzo.Code.Data.Vec.du542 v3)
                                                     (coe du968 v0 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name988 = "Data.Vec.Properties.proof-irrelevance-[]="
d988 = erased
name1006 = "Data.Vec.Properties.[]=\8596lookup"
d1006 v0 v1 v2 v3 v4 v5 = du1006 v2 v4 v5
du1006 v0 v1 v2
  = coe MAlonzo.Code.Function.Inverse.C173
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du210
         (coe MAlonzo.Code.Relation.Binary.C85 erased erased
            (coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased))
         erased)
      (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du210
         (coe MAlonzo.Code.Relation.Binary.C85 erased erased
            (coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased))
         (coe d1034 erased erased erased erased v1 erased erased v0 v2))
      (coe MAlonzo.Code.Function.Inverse.C109 erased erased)
name1024 = "Data.Vec.Properties._.to"
d1024 = erased
name1034 = "Data.Vec.Properties._.from"
d1034 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du1034 v4 v7 v8
du1034 v0 v1 v2
  = case coe v1 of
        MAlonzo.Code.Data.Fin.C8 v3 -> case coe v2 of
                                           MAlonzo.Code.Data.Vec.C22 v4 v5 v6 -> coe
                                                                                   MAlonzo.Code.Data.Vec.C74
                                                                                   v3
                                                                                   v0
                                                                                   v6
                                           _ -> coe MAlonzo.RTE.mazUnreachableError
        MAlonzo.Code.Data.Fin.C14 v3 v4 -> case coe v2 of
                                               MAlonzo.Code.Data.Vec.C22 v5 v6 v7 -> coe
                                                                                       MAlonzo.Code.Data.Vec.C88
                                                                                       v3
                                                                                       v4
                                                                                       v0
                                                                                       v6
                                                                                       v7
                                                                                       (coe du1034
                                                                                          v0
                                                                                          v4
                                                                                          v7)
                                               _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1060 = "Data.Vec.Properties.[]\8788-idempotent"
d1060 = erased
name1088 = "Data.Vec.Properties.[]\8788-commutes"
d1088 = erased
name1130 = "Data.Vec.Properties.[]\8788-updates"
d1130 v0 v1 v2 v3 v4 = du1130 v3 v4
du1130 v0 v1
  = case coe v0 of
        MAlonzo.Code.Data.Vec.C22 v2 v3 v4 -> case coe v1 of
                                                  MAlonzo.Code.Data.Fin.C8 v5 -> coe
                                                                                   (\ v6 ->
                                                                                      coe
                                                                                        MAlonzo.Code.Data.Vec.C74
                                                                                        v2
                                                                                        v6
                                                                                        v4)
                                                  MAlonzo.Code.Data.Fin.C14 v5 v6 -> coe
                                                                                       (\ v7 ->
                                                                                          coe
                                                                                            MAlonzo.Code.Data.Vec.C88
                                                                                            v2
                                                                                            v6
                                                                                            v7
                                                                                            v3
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.du728
                                                                                               v4
                                                                                               v6
                                                                                               v7)
                                                                                            (coe
                                                                                               du1130
                                                                                               v4
                                                                                               v6
                                                                                               v7))
                                                  _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1158 = "Data.Vec.Properties.[]\8788-minimal"
d1158 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du1158 v1 v3 v4 v5 v6 v7 v8 v9
du1158 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
        MAlonzo.Code.Data.Vec.C22 v8 v9 v10 -> case coe v3 of
                                                   MAlonzo.Code.Data.Fin.C8 v11 -> case coe v7 of
                                                                                       MAlonzo.Code.Data.Vec.C74
                                                                                         v12 v13
                                                                                         v14 -> coe
                                                                                                  MAlonzo.Code.Function.du158
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Empty.d10
                                                                                                     v0
                                                                                                     erased)
                                                                                                  (coe
                                                                                                     v6
                                                                                                     erased)
                                                                                       MAlonzo.Code.Data.Vec.C88
                                                                                         v12 v13 v14
                                                                                         v15 v16
                                                                                         v17 -> case
                                                                                                  coe
                                                                                                    v2
                                                                                                  of
                                                                                                    MAlonzo.Code.Data.Fin.C14
                                                                                                      v18
                                                                                                      v19 -> coe
                                                                                                               MAlonzo.Code.Data.Vec.C88
                                                                                                               v8
                                                                                                               v19
                                                                                                               v4
                                                                                                               v5
                                                                                                               v10
                                                                                                               v17
                                                                                                    _ -> coe
                                                                                                           MAlonzo.RTE.mazUnreachableError
                                                                                       _ -> coe
                                                                                              MAlonzo.RTE.mazUnreachableError
                                                   MAlonzo.Code.Data.Fin.C14 v11 v12 -> case coe v7
                                                                                          of
                                                                                            MAlonzo.Code.Data.Vec.C74
                                                                                              v13
                                                                                              v14
                                                                                              v15 -> coe
                                                                                                       MAlonzo.Code.Data.Vec.C74
                                                                                                       v8
                                                                                                       v9
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Data.Vec.du728
                                                                                                          v10
                                                                                                          v12
                                                                                                          v5)
                                                                                            MAlonzo.Code.Data.Vec.C88
                                                                                              v13
                                                                                              v14
                                                                                              v15
                                                                                              v16
                                                                                              v17
                                                                                              v18 -> case
                                                                                                       coe
                                                                                                         v2
                                                                                                       of
                                                                                                         MAlonzo.Code.Data.Fin.C14
                                                                                                           v19
                                                                                                           v20 -> coe
                                                                                                                    MAlonzo.Code.Data.Vec.C88
                                                                                                                    v8
                                                                                                                    v20
                                                                                                                    v4
                                                                                                                    v9
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Data.Vec.du728
                                                                                                                       v10
                                                                                                                       v12
                                                                                                                       v5)
                                                                                                                    (coe
                                                                                                                       du1158
                                                                                                                       v0
                                                                                                                       v10
                                                                                                                       v20
                                                                                                                       v12
                                                                                                                       v4
                                                                                                                       v5
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Function.d38
                                                                                                                          erased
                                                                                                                          erased
                                                                                                                          erased
                                                                                                                          erased
                                                                                                                          erased
                                                                                                                          erased
                                                                                                                          (\ v21
                                                                                                                             ->
                                                                                                                             v6)
                                                                                                                          erased)
                                                                                                                       v18)
                                                                                                         _ -> coe
                                                                                                                MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> coe
                                                                                                   MAlonzo.RTE.mazUnreachableError
                                                   _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1210 = "Data.Vec.Properties.map-[]\8788"
d1210 = erased
name1238 = "Data.Vec.Properties.[]\8788-lookup"
d1238 = erased
name1266 = "Data.Vec.Properties.[]\8788-++-inject+"
d1266 = erased