{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.RingSolver where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Algebra.Morphism
import qualified MAlonzo.Code.Algebra.Operations
import qualified
       MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing
import qualified MAlonzo.Code.Algebra.RingSolver.Lemmas
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Vec
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified MAlonzo.Code.Relation.Binary.Reflection
import qualified MAlonzo.Code.Relation.Nullary
name20 = "Algebra.RingSolver._.lemma\8320"
d20 v0 v1 v2 v3 v4 v5 v6 = du20 v4
du20 v0
  = coe MAlonzo.Code.Algebra.RingSolver.Lemmas.d176 erased erased
      erased
      erased
      v0
      erased
name22 = "Algebra.RingSolver._.lemma\8321"
d22 v0 v1 v2 v3 v4 v5 v6 = du22 v4
du22 v0
  = coe MAlonzo.Code.Algebra.RingSolver.Lemmas.d196 erased erased
      erased
      erased
      v0
      erased
name24 = "Algebra.RingSolver._.lemma\8322"
d24 v0 v1 v2 v3 v4 v5 v6 = du24 v4
du24 v0
  = coe MAlonzo.Code.Algebra.RingSolver.Lemmas.d216 erased erased
      erased
      erased
      v0
      erased
name26 = "Algebra.RingSolver._.lemma\8323"
d26 v0 v1 v2 v3 v4 v5 v6 = du26 v4
du26 v0
  = coe MAlonzo.Code.Algebra.RingSolver.Lemmas.d240 erased erased
      erased
      erased
      v0
      erased
name28 = "Algebra.RingSolver._.lemma\8324"
d28 v0 v1 v2 v3 v4 v5 v6 = du28 v4
du28 v0
  = coe MAlonzo.Code.Algebra.RingSolver.Lemmas.d260 erased erased
      erased
      erased
      v0
      erased
name30 = "Algebra.RingSolver._.lemma\8325"
d30 v0 v1 v2 v3 v4 v5 v6 = du30 v4
du30 v0
  = coe MAlonzo.Code.Algebra.RingSolver.Lemmas.d284 erased erased
      erased
      erased
      v0
      erased
name32 = "Algebra.RingSolver._.lemma\8326"
d32 v0 v1 v2 v3 v4 v5 v6 = du32 v4
du32 v0
  = coe MAlonzo.Code.Algebra.RingSolver.Lemmas.d292 erased erased
      erased
      erased
      v0
      erased
name34 = "Algebra.RingSolver._.lemma\8327"
d34 v0 v1 v2 v3 v4 v5 v6 = du34 v4
du34 v0
  = coe MAlonzo.Code.Algebra.RingSolver.Lemmas.d300 erased erased
      erased
      erased
      v0
      erased
name38 = "Algebra.RingSolver.C._*_"
d38 v0 v1 v2 v3 v4 v5 v6 = du38 v3
du38 v0 = coe MAlonzo.Code.Algebra.d964 v0
name40 = "Algebra.RingSolver.C._+_"
d40 v0 v1 v2 v3 v4 v5 v6 = du40 v3
du40 v0 = coe MAlonzo.Code.Algebra.d962 v0
name42 = "Algebra.RingSolver.C.-_"
d42 v0 v1 v2 v3 v4 v5 v6 = du42 v3
du42 v0 = coe MAlonzo.Code.Algebra.d966 v0
name44 = "Algebra.RingSolver.C.0#"
d44 v0 v1 v2 v3 v4 v5 v6 = du44 v3
du44 v0 = coe MAlonzo.Code.Algebra.d968 v0
name46 = "Algebra.RingSolver.C.1#"
d46 v0 v1 v2 v3 v4 v5 v6 = du46 v3
du46 v0 = coe MAlonzo.Code.Algebra.d970 v0
name48 = "Algebra.RingSolver.C.Carrier"
d48 = erased
name52 = "Algebra.RingSolver._._*_"
d52 v0 v1 v2 v3 v4 v5 v6 = du52 v4
du52 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
name54 = "Algebra.RingSolver._._+_"
d54 v0 v1 v2 v3 v4 v5 v6 = du54 v4
du54 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
name56 = "Algebra.RingSolver._._\8776_"
d56 = erased
name64 = "Algebra.RingSolver._.\8729-cong"
d64 v0 v1 v2 v3 v4 v5 v6 = du64 v4
du64 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du182
      v0
name84 = "Algebra.RingSolver._.\8729-cong"
d84 v0 v1 v2 v3 v4 v5 v6 = du84 v4
du84 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du196
      v0
name86 = "Algebra.RingSolver._.identity"
d86 v0 v1 v2 v3 v4 v5 v6 = du86 v4
du86 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du198
      v0
name98 = "Algebra.RingSolver._.-_"
d98 v0 v1 v2 v3 v4 v5 v6 = du98 v4
du98 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d168 v0
name104 = "Algebra.RingSolver._.-\8255cong"
d104 v0 v1 v2 v3 v4 v5 v6 = du104 v4
du104 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d62
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d174 v0)
name106 = "Algebra.RingSolver._.0#"
d106 v0 v1 v2 v3 v4 v5 v6 = du106 v4
du106 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0
name108 = "Algebra.RingSolver._.1#"
d108 v0 v1 v2 v3 v4 v5 v6 = du108 v4
du108 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d172 v0
name110 = "Algebra.RingSolver._.Carrier"
d110 = erased
name136 = "Algebra.RingSolver._.refl"
d136 v0 v1 v2 v3 v4 v5 v6 = du136 v4
du136 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du230
      v0
name140 = "Algebra.RingSolver._.semiring"
d140 v0 v1 v2 v3 v4 v5 v6 = du140 v4
du140 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du258
      v0
name142 = "Algebra.RingSolver._.setoid"
d142 v0 v1 v2 v3 v4 v5 v6 = du142 v4
du142 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du260
      v0
name144 = "Algebra.RingSolver._.sym"
d144 v0 v1 v2 v3 v4 v5 v6 = du144 v4
du144 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du234
      v0
name146 = "Algebra.RingSolver._.trans"
d146 v0 v1 v2 v3 v4 v5 v6 = du146 v4
du146 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du236
      v0
name148 = "Algebra.RingSolver._.zero"
d148 v0 v1 v2 v3 v4 v5 v6 = du148 v4
du148 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du238
      v0
name196 = "Algebra.RingSolver._.Op\8322"
d196 = erased
name200 = "Algebra.RingSolver._.*-homo"
d200 v0 v1 v2 v3 v4 v5 v6 = du200 v5
du200 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d554 v0
name202 = "Algebra.RingSolver._.+-homo"
d202 v0 v1 v2 v3 v4 v5 v6 = du202 v5
du202 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d552 v0
name204 = "Algebra.RingSolver._.-\8255homo"
d204 v0 v1 v2 v3 v4 v5 v6 = du204 v5
du204 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d556 v0
name206 = "Algebra.RingSolver._.0-homo"
d206 v0 v1 v2 v3 v4 v5 v6 = du206 v5
du206 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d558 v0
name208 = "Algebra.RingSolver._.1-homo"
d208 v0 v1 v2 v3 v4 v5 v6 = du208 v5
du208 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d560 v0
name210 = "Algebra.RingSolver._.\10214_\10215"
d210 v0 v1 v2 v3 v4 v5 v6 = du210 v5
du210 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d550 v0
name214 = "Algebra.RingSolver._._^_"
d214 v0 v1 v2 v3 v4 v5 v6 = du214 v4
du214 v0
  = coe MAlonzo.Code.Algebra.Operations.d130 erased erased
      (coe du140 v0)
name222 = "Algebra.RingSolver._.^-cong"
d222 v0 v1 v2 v3 v4 v5 v6 = du222 v4
du222 v0
  = coe MAlonzo.Code.Algebra.Operations.d260 erased erased
      (coe du140 v0)
name242 = "Algebra.RingSolver._._\8718"
d242 v0 v1 v2 v3 v4 v5 v6 = du242 v4
du242 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe du142 v0)
name244 = "Algebra.RingSolver._._\8764\10216_\10217_"
d244 v0 v1 v2 v3 v4 v5 v6 = du244 v4
du244 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40 (coe du142 v0)
name258 = "Algebra.RingSolver.Op"
d258 a0 a1 a2 a3 a4 a5 a6 = ()

data T258 = C260
          | C262
name266 = "Algebra.RingSolver.Polynomial"
d266 a0 a1 a2 a3 a4 a5 a6 a7 = ()

data T266 a0 a1 a2 = C276 a0 a1 a2
                   | C280 a0
                   | C284 a0
                   | C290 a0 a1
                   | C294 a0
name298 = "Algebra.RingSolver._:+_"
d298 v0 v1 v2 = du298
du298 = coe C276 (coe C260)
name302 = "Algebra.RingSolver._:*_"
d302 v0 v1 v2 = du302
du302 = coe C276 (coe C262)
name306 = "Algebra.RingSolver._:-_"
d306 v0 v1 v2 v3 v4 = du306 v3 v4
du306 v0 v1 = coe C276 (coe C260) v0 (coe C294 v1)
name312 = "Algebra.RingSolver.sem"
d312 v0 v1 v2 v3 v4 v5 v6 v7 = du312 v4 v7
du312 v0 v1
  = case coe v1 of
        C260 -> coe du54 v0
        C262 -> coe du52 v0
        _ -> coe MAlonzo.RTE.mazUnreachableError
name316 = "Algebra.RingSolver.\10214_\10215"
d316 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du316 v4 v5 v8 v9
du316 v0 v1 v2 v3
  = case coe v2 of
        C276 v4 v5 v6 -> coe MAlonzo.Code.Function.du176
                           (coe du316 v0 v1 v5 v3)
                           (coe du312 v0 v4)
                           (coe du316 v0 v1 v6 v3)
        C280 v4 -> coe du210 v1 v4
        C284 v4 -> coe MAlonzo.Code.Data.Vec.du696 v4 v3
        C290 v4 v5 -> coe du214 v0 (coe du316 v0 v1 v4 v3) v5
        C294 v4 -> coe du98 v0 (coe du316 v0 v1 v4 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name344 = "Algebra.RingSolver.HNF"
d344 a0 a1 a2 a3 a4 a5 a6 a7 = ()

data T344 a0 a1 a2 = C350 a0
                   | C354 a0 a1 a2
name346 = "Algebra.RingSolver.Normal"
d346 a0 a1 a2 a3 a4 a5 a6 a7 = ()

data T346 a0 a1 = C356 a0
                | C360 a0 a1
name364 = "Algebra.RingSolver.\10214_\10215H"
d364 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
        C350 v10 -> coe du106 v4
        C354 v10 v11 v12 -> case coe v9 of
                                MAlonzo.Code.Data.Vec.C22 v13 v14 v15 -> coe du54 v4
                                                                           (coe du52 v4
                                                                              (coe d364 v0 v1 v2 v3
                                                                                 v4
                                                                                 v5
                                                                                 v6
                                                                                 v7
                                                                                 v11
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                    v7
                                                                                    v14
                                                                                    v15))
                                                                              v14)
                                                                           (coe du368 v0 v1 v2 v3 v4
                                                                              v5
                                                                              v6
                                                                              v12
                                                                              v15)
                                _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name368 = "Algebra.RingSolver.\10214_\10215N"
d368 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du368 v0 v1 v2 v3 v4 v5 v6 v8 v9
du368 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
        C356 v9 -> coe du210 v5 v9
        C360 v9 v10 -> coe d364 v0 v1 v2 v3 v4 v5 v6 v9 v10 v8
        _ -> coe MAlonzo.RTE.mazUnreachableError
name384 = "Algebra.RingSolver._\8776H_"
d384 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()

data T384 a0 a1 a2 a3 a4 a5 a6 = C394 a0
                               | C406 a0 a1 a2 a3 a4 a5 a6
name388 = "Algebra.RingSolver._\8776N_"
d388 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()

data T388 a0 a1 a2 a3 = C412 a0 a1 a2
                      | C420 a0 a1 a2 a3
name424 = "Algebra.RingSolver._\8799H_"
d424 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du424 v0 v1 v2 v3 v4 v5 v6 v8 v9
du424 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
        C350 v9 -> case coe v8 of
                       C350 v10 -> coe MAlonzo.Code.Relation.Nullary.C22 (coe C394 v9)
                       C354 v10 v11 v12 -> coe MAlonzo.Code.Relation.Nullary.C26 erased
                       _ -> coe MAlonzo.RTE.mazUnreachableError
        C354 v9 v10 v11 -> case coe v8 of
                               C350 v12 -> coe MAlonzo.Code.Relation.Nullary.C26 erased
                               C354 v12 v13 v14 -> let v15
                                                         = coe du424 v0 v1 v2 v3 v4 v5 v6 v10 v13
                                                     in
                                                     let v16
                                                           = coe du428 v0 v1 v2 v3 v4 v5 v6 v11 v14
                                                       in
                                                       let v17
                                                             = case coe v16 of
                                                                   MAlonzo.Code.Relation.Nullary.C26
                                                                     v17 -> coe
                                                                              MAlonzo.Code.Relation.Nullary.C26
                                                                              erased
                                                                   _ -> coe
                                                                          MAlonzo.RTE.mazUnreachableError
                                                         in
                                                         case coe v15 of
                                                             MAlonzo.Code.Relation.Nullary.C22
                                                               v18 -> case coe v16 of
                                                                          MAlonzo.Code.Relation.Nullary.C22
                                                                            v19 -> coe
                                                                                     MAlonzo.Code.Relation.Nullary.C22
                                                                                     (coe C406 v9
                                                                                        v10
                                                                                        v13
                                                                                        v11
                                                                                        v14
                                                                                        v18
                                                                                        v19)
                                                                          _ -> coe v17
                                                             MAlonzo.Code.Relation.Nullary.C26
                                                               v18 -> let v19
                                                                            = coe
                                                                                MAlonzo.Code.Relation.Nullary.C26
                                                                                erased
                                                                        in
                                                                        case coe v16 of
                                                                            MAlonzo.Code.Relation.Nullary.C26
                                                                              v20 -> coe
                                                                                       MAlonzo.Code.Relation.Nullary.C26
                                                                                       erased
                                                                            _ -> coe v19
                                                             _ -> coe v17
                               _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name428 = "Algebra.RingSolver._\8799N_"
d428 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du428 v0 v1 v2 v3 v4 v5 v6 v8 v9
du428 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
        C356 v9 -> case coe v8 of
                       C356 v10 -> let v11 = coe v6 v9 v10 in
                                     case coe v11 of
                                         MAlonzo.Code.Relation.Nullary.C22 v12 -> coe
                                                                                    MAlonzo.Code.Relation.Nullary.C22
                                                                                    (coe C412 v9 v10
                                                                                       v12)
                                         MAlonzo.Code.Relation.Nullary.C26 v12 -> coe
                                                                                    MAlonzo.Code.Relation.Nullary.C26
                                                                                    erased
                                         _ -> coe MAlonzo.RTE.mazUnreachableError
                       _ -> coe MAlonzo.RTE.mazUnreachableError
        C360 v9 v10 -> case coe v8 of
                           C360 v11 v12 -> let v13 = coe du424 v0 v1 v2 v3 v4 v5 v6 v10 v12 in
                                             case coe v13 of
                                                 MAlonzo.Code.Relation.Nullary.C22 v14 -> coe
                                                                                            MAlonzo.Code.Relation.Nullary.C22
                                                                                            (coe
                                                                                               C420
                                                                                               v9
                                                                                               v10
                                                                                               v12
                                                                                               v14)
                                                 MAlonzo.Code.Relation.Nullary.C26 v14 -> coe
                                                                                            MAlonzo.Code.Relation.Nullary.C26
                                                                                            erased
                                                 _ -> coe MAlonzo.RTE.mazUnreachableError
                           _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name538 = "Algebra.RingSolver.\10214_\10215H-cong"
d538 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du538 v0 v1 v2 v3 v4 v5 v6 v7 v10 v11
du538 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
        C394 v10 -> coe du136 v4
                      (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 (coe C350 v7) v9)
        C406 v10 v11 v12 v13 v14 v15 v16 -> case coe v9 of
                                                MAlonzo.Code.Data.Vec.C22 v17 v18 v19 -> coe
                                                                                           MAlonzo.Code.Function.du176
                                                                                           (coe
                                                                                              MAlonzo.Code.Function.du176
                                                                                              (coe
                                                                                                 du538
                                                                                                 v0
                                                                                                 v1
                                                                                                 v2
                                                                                                 v3
                                                                                                 v4
                                                                                                 v5
                                                                                                 v6
                                                                                                 v7
                                                                                                 v15
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                    v7
                                                                                                    v18
                                                                                                    v19))
                                                                                              (coe
                                                                                                 du64
                                                                                                 v4
                                                                                                 (coe
                                                                                                    d364
                                                                                                    v0
                                                                                                    v1
                                                                                                    v2
                                                                                                    v3
                                                                                                    v4
                                                                                                    v5
                                                                                                    v6
                                                                                                    v7
                                                                                                    v11
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                       v7
                                                                                                       v18
                                                                                                       v19))
                                                                                                 (coe
                                                                                                    d364
                                                                                                    v0
                                                                                                    v1
                                                                                                    v2
                                                                                                    v3
                                                                                                    v4
                                                                                                    v5
                                                                                                    v6
                                                                                                    v7
                                                                                                    v12
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                       v7
                                                                                                       v18
                                                                                                       v19))
                                                                                                 v18
                                                                                                 v18)
                                                                                              (coe
                                                                                                 du136
                                                                                                 v4
                                                                                                 v18))
                                                                                           (coe du84
                                                                                              v4
                                                                                              (coe
                                                                                                 MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                 v4
                                                                                                 (coe
                                                                                                    d364
                                                                                                    v0
                                                                                                    v1
                                                                                                    v2
                                                                                                    v3
                                                                                                    v4
                                                                                                    v5
                                                                                                    v6
                                                                                                    v7
                                                                                                    v11
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                       v7
                                                                                                       v18
                                                                                                       v19))
                                                                                                 v18)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                 v4
                                                                                                 (coe
                                                                                                    d364
                                                                                                    v0
                                                                                                    v1
                                                                                                    v2
                                                                                                    v3
                                                                                                    v4
                                                                                                    v5
                                                                                                    v6
                                                                                                    v7
                                                                                                    v12
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                       v7
                                                                                                       v18
                                                                                                       v19))
                                                                                                 v18)
                                                                                              (coe
                                                                                                 du368
                                                                                                 v0
                                                                                                 v1
                                                                                                 v2
                                                                                                 v3
                                                                                                 v4
                                                                                                 v5
                                                                                                 v6
                                                                                                 v13
                                                                                                 v19)
                                                                                              (coe
                                                                                                 du368
                                                                                                 v0
                                                                                                 v1
                                                                                                 v2
                                                                                                 v3
                                                                                                 v4
                                                                                                 v5
                                                                                                 v6
                                                                                                 v14
                                                                                                 v19))
                                                                                           (coe
                                                                                              du548
                                                                                              v0
                                                                                              v1
                                                                                              v2
                                                                                              v3
                                                                                              v4
                                                                                              v5
                                                                                              v6
                                                                                              v16
                                                                                              v19)
                                                _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name548 = "Algebra.RingSolver.\10214_\10215N-cong"
d548 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du548 v0 v1 v2 v3 v4 v5 v6 v10 v11
du548 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
        C412 v9 v10 v11 -> coe v11
        C420 v9 v10 v11 v12 -> coe du538 v0 v1 v2 v3 v4 v5 v6 v9 v12 v8
        _ -> coe MAlonzo.RTE.mazUnreachableError
name566 = "Algebra.RingSolver.0H"
d566 v0 v1 = du566
du566 = C350
name570 = "Algebra.RingSolver.0N"
d570 v0 v1 v2 v3 v4 v5 v6 v7 = du570 v3 v7
du570 v0 v1
  = case coe v1 of
        0 -> coe C356 (coe du44 v0)
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in coe C360 v2 (coe C350 v2)
name576 = "Algebra.RingSolver.1H"
d576 v0 v1 v2 v3 v4 v5 v6 v7
  = coe C354 v7 (coe C350 v7) (coe d580 v0 v1 v2 v3 v4 v5 v6 v7)
name580 = "Algebra.RingSolver.1N"
d580 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
        0 -> coe C356 (coe du46 v3)
        _ -> let v8
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v7
                       (1 :: Integer)
               in coe C360 v8 (coe d576 v0 v1 v2 v3 v4 v5 v6 v8)
name588 = "Algebra.RingSolver._*x+HN_"
d588 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
        C350 v10 -> let v11
                          = coe du428 v0 v1 v2 v3 v4 v5 v6 v9 (coe du570 v3 v7)
                      in
                      case coe v11 of
                          MAlonzo.Code.Relation.Nullary.C22 v12 -> coe C350 v7
                          MAlonzo.Code.Relation.Nullary.C26 v12 -> coe C354 v7 (coe C350 v7)
                                                                     v9
                          _ -> coe MAlonzo.RTE.mazUnreachableError
        C354 v10 v11 v12 -> coe C354 v7 (coe C354 v7 v11 v12) v9
        _ -> coe MAlonzo.RTE.mazUnreachableError
name612 = "Algebra.RingSolver._+H_"
d612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = let v10
          = case coe v9 of
                C350 v10 -> coe v8
                _ -> coe MAlonzo.RTE.mazUnreachableError
      in
      case coe v8 of
          C350 v11 -> coe v9
          C354 v11 v12 v13 -> case coe v9 of
                                  C350 v14 -> coe C354 v11 v12 v13
                                  C354 v14 v15 v16 -> coe d588 v0 v1 v2 v3 v4 v5 v6 v7
                                                        (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 v12 v15)
                                                        (coe du616 v0 v1 v2 v3 v4 v5 v6 v13 v16)
                                  _ -> coe v10
          _ -> coe v10
name616 = "Algebra.RingSolver._+N_"
d616 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du616 v0 v1 v2 v3 v4 v5 v6 v8 v9
du616 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
        C356 v9 -> case coe v8 of
                       C356 v10 -> coe C356 (coe du40 v3 v9 v10)
                       _ -> coe MAlonzo.RTE.mazUnreachableError
        C360 v9 v10 -> case coe v8 of
                           C360 v11 v12 -> coe C360 v9
                                             (coe d612 v0 v1 v2 v3 v4 v5 v6 v9 v10 v12)
                           _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name640 = "Algebra.RingSolver._*x+H_"
d640 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
        C350 v10 -> case coe v8 of
                        C350 v11 -> coe C350 v7
                        C354 v11 v12 v13 -> coe C354 v7 (coe C354 v7 v12 v13)
                                              (coe du570 v3 v7)
                        _ -> coe MAlonzo.RTE.mazUnreachableError
        C354 v10 v11 v12 -> coe d588 v0 v1 v2 v3 v4 v5 v6 v7
                              (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v11)
                              v12
        _ -> coe MAlonzo.RTE.mazUnreachableError
name654 = "Algebra.RingSolver._*NH_"
d654 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
        C350 v10 -> coe C350 v7
        C354 v10 v11 v12 -> let v13
                                  = coe du428 v0 v1 v2 v3 v4 v5 v6 v8 (coe du570 v3 v7)
                              in
                              case coe v13 of
                                  MAlonzo.Code.Relation.Nullary.C22 v14 -> coe C350 v7
                                  MAlonzo.Code.Relation.Nullary.C26 v14 -> coe C354 v7
                                                                             (coe d654 v0 v1 v2 v3
                                                                                v4
                                                                                v5
                                                                                v6
                                                                                v7
                                                                                v8
                                                                                v11)
                                                                             (coe du666 v0 v1 v2 v3
                                                                                v4
                                                                                v5
                                                                                v6
                                                                                v8
                                                                                v12)
                                  _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name658 = "Algebra.RingSolver._*HN_"
d658 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
        C350 v10 -> coe C350 v7
        C354 v10 v11 v12 -> let v13
                                  = coe du428 v0 v1 v2 v3 v4 v5 v6 v9 (coe du570 v3 v7)
                              in
                              case coe v13 of
                                  MAlonzo.Code.Relation.Nullary.C22 v14 -> coe C350 v7
                                  MAlonzo.Code.Relation.Nullary.C26 v14 -> coe C354 v7
                                                                             (coe d658 v0 v1 v2 v3
                                                                                v4
                                                                                v5
                                                                                v6
                                                                                v7
                                                                                v11
                                                                                v9)
                                                                             (coe du666 v0 v1 v2 v3
                                                                                v4
                                                                                v5
                                                                                v6
                                                                                v12
                                                                                v9)
                                  _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name662 = "Algebra.RingSolver._*H_"
d662 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
        C350 v10 -> coe C350 v7
        C354 v10 v11 v12 -> case coe v9 of
                                C350 v13 -> coe C350 v7
                                C354 v13 v14 v15 -> coe d588 v0 v1 v2 v3 v4 v5 v6 v7
                                                      (coe d640 v0 v1 v2 v3 v4 v5 v6 v7
                                                         (coe d662 v0 v1 v2 v3 v4 v5 v6 v7 v11 v14)
                                                         (coe d612 v0 v1 v2 v3 v4 v5 v6 v7
                                                            (coe d658 v0 v1 v2 v3 v4 v5 v6 v7 v11
                                                               v15)
                                                            (coe d654 v0 v1 v2 v3 v4 v5 v6 v7 v12
                                                               v14)))
                                                      (coe du666 v0 v1 v2 v3 v4 v5 v6 v12 v15)
                                _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name666 = "Algebra.RingSolver._*N_"
d666 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du666 v0 v1 v2 v3 v4 v5 v6 v8 v9
du666 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
        C356 v9 -> case coe v8 of
                       C356 v10 -> coe C356 (coe du38 v3 v9 v10)
                       _ -> coe MAlonzo.RTE.mazUnreachableError
        C360 v9 v10 -> case coe v8 of
                           C360 v11 v12 -> coe C360 v9
                                             (coe d662 v0 v1 v2 v3 v4 v5 v6 v9 v10 v12)
                           _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name742 = "Algebra.RingSolver._^N_"
d742 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
        0 -> coe d580 v0 v1 v2 v3 v4 v5 v6 v7
        _ -> let v10
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v9
                       (1 :: Integer)
               in
               coe du666 v0 v1 v2 v3 v4 v5 v6 v8
                 (coe d742 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10)
name752 = "Algebra.RingSolver.-H_"
d752 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe d654 v0 v1 v2 v3 v4 v5 v6 v7
      (coe du756 v0 v1 v2 v3 v4 v5 v6 (coe d580 v0 v1 v2 v3 v4 v5 v6 v7))
      v8
name756 = "Algebra.RingSolver.-N_"
d756 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du756 v0 v1 v2 v3 v4 v5 v6 v8
du756 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
        C356 v8 -> coe C356 (coe du42 v3 v8)
        C360 v8 v9 -> coe C360 v8 (coe d752 v0 v1 v2 v3 v4 v5 v6 v8 v9)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name766 = "Algebra.RingSolver.normalise-con"
d766 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
        0 -> coe C356 v8
        _ -> let v9
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v7
                       (1 :: Integer)
               in
               coe C360 v9
                 (coe d588 v0 v1 v2 v3 v4 v5 v6 v9 (coe C350 v9)
                    (coe d766 v0 v1 v2 v3 v4 v5 v6 v9 v8))
name776 = "Algebra.RingSolver.normalise-var"
d776 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du776 v0 v1 v2 v3 v4 v5 v6 v8
du776 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
        MAlonzo.Code.Data.Fin.C8 v8 -> coe C360 v8
                                         (coe C354 v8
                                            (coe C354 v8 (coe C350 v8)
                                               (coe d580 v0 v1 v2 v3 v4 v5 v6 v8))
                                            (coe du570 v3 v8))
        MAlonzo.Code.Data.Fin.C14 v8 v9 -> coe C360 v8
                                             (coe d588 v0 v1 v2 v3 v4 v5 v6 v8 (coe C350 v8)
                                                (coe du776 v0 v1 v2 v3 v4 v5 v6 v9))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name782 = "Algebra.RingSolver.normalise"
d782 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
        C276 v9 v10 v11 -> case coe v9 of
                               C260 -> coe du616 v0 v1 v2 v3 v4 v5 v6
                                         (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v10)
                                         (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v11)
                               C262 -> coe du666 v0 v1 v2 v3 v4 v5 v6
                                         (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v10)
                                         (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v11)
                               _ -> coe MAlonzo.RTE.mazUnreachableError
        C280 v9 -> coe d766 v0 v1 v2 v3 v4 v5 v6 v7 v9
        C284 v9 -> coe du776 v0 v1 v2 v3 v4 v5 v6 v9
        C290 v9 v10 -> coe d742 v0 v1 v2 v3 v4 v5 v6 v7
                         (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v9)
                         v10
        C294 v9 -> coe du756 v0 v1 v2 v3 v4 v5 v6
                     (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v9)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name804 = "Algebra.RingSolver.\10214_\10215\8595"
d804 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe du368 v0 v1 v2 v3 v4 v5 v6
      (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v8)
      v9
name811 = "Algebra.RingSolver..absurdlambda"
d811 = erased
name814 = "Algebra.RingSolver.0N-homo"
d814 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du814 v0 v1 v2 v3 v4 v5 v6 v8
du814 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
        MAlonzo.Code.Data.Vec.C14 -> coe du206 v5
        MAlonzo.Code.Data.Vec.C22 v8 v9 v10 -> coe du136 v4
                                                 (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                    (coe du570 v3
                                                       (coe
                                                          ((Prelude.+) :: Integer -> Integer -> Integer)
                                                          (1 :: Integer)
                                                          v8))
                                                    (coe MAlonzo.Code.Data.Vec.C22 v8 v9 v10))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name826 = "Algebra.RingSolver.0\8776\10214\&0\10215"
d826 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe du144 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
      (coe du106 v4)
      (coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
         (coe du244 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
            (coe du368 v0 v1 v2 v3 v4 v5 v6 (coe du570 v3 v7) v10)
            (coe du106 v4)
            (coe du548 v0 v1 v2 v3 v4 v5 v6 v9 v10)
            (coe du244 v4
               (coe du368 v0 v1 v2 v3 v4 v5 v6 (coe du570 v3 v7) v10)
               (coe du106 v4)
               (coe du106 v4)
               (coe du814 v0 v1 v2 v3 v4 v5 v6 v10)
               (coe du242 v4 (coe du106 v4)))))
name838 = "Algebra.RingSolver.1N-homo"
d838 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du838 v0 v1 v2 v3 v4 v5 v6 v8
du838 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
        MAlonzo.Code.Data.Vec.C14 -> coe du208 v5
        MAlonzo.Code.Data.Vec.C22 v8 v9 v10 -> coe
                                                 MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                 (coe du244 v4
                                                    (coe du54 v4 (coe du52 v4 (coe du106 v4) v9)
                                                       (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                          (coe d580 v0 v1 v2 v3 v4 v5 v6 v8)
                                                          v10))
                                                    (coe
                                                       MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                       v4
                                                       (coe du52 v4 (coe du106 v4) v9)
                                                       (coe du108 v4))
                                                    (coe du108 v4)
                                                    (coe MAlonzo.Code.Function.du176
                                                       (coe du136 v4
                                                          (coe du52 v4 (coe du106 v4) v9))
                                                       (coe du84 v4 (coe du52 v4 (coe du106 v4) v9)
                                                          (coe du52 v4 (coe du106 v4) v9)
                                                          (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                             (coe d580 v0 v1 v2 v3 v4 v5 v6 v8)
                                                             v10)
                                                          (coe du108 v4))
                                                       (coe du838 v0 v1 v2 v3 v4 v5 v6 v10))
                                                    (coe du244 v4
                                                       (coe du54 v4 (coe du52 v4 (coe du106 v4) v9)
                                                          (coe du108 v4))
                                                       (coe du108 v4)
                                                       (coe du108 v4)
                                                       (coe du32 v4 (coe du108 v4) v9)
                                                       (coe du242 v4 (coe du108 v4))))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name852 = "Algebra.RingSolver.*x+HN\8776*x+"
d852 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v8 of
        C350 v11 -> case coe v10 of
                        MAlonzo.Code.Data.Vec.C22 v12 v13 v14 -> let v15
                                                                       = coe du428 v0 v1 v2 v3 v4 v5
                                                                           v6
                                                                           v9
                                                                           (coe du570 v3 v7)
                                                                   in
                                                                   case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.C22
                                                                         v16 -> coe
                                                                                  MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                                                  (coe du244 v4
                                                                                     (coe du106 v4)
                                                                                     (coe du368 v0
                                                                                        v1
                                                                                        v2
                                                                                        v3
                                                                                        v4
                                                                                        v5
                                                                                        v6
                                                                                        v9
                                                                                        v14)
                                                                                     (coe du54 v4
                                                                                        (coe du52 v4
                                                                                           (coe
                                                                                              du106
                                                                                              v4)
                                                                                           v13)
                                                                                        (coe du368
                                                                                           v0
                                                                                           v1
                                                                                           v2
                                                                                           v3
                                                                                           v4
                                                                                           v5
                                                                                           v6
                                                                                           v9
                                                                                           v14))
                                                                                     (coe d826 v0 v1
                                                                                        v2
                                                                                        v3
                                                                                        v4
                                                                                        v5
                                                                                        v6
                                                                                        v7
                                                                                        v9
                                                                                        v16
                                                                                        v14)
                                                                                     (coe du244 v4
                                                                                        (coe du368
                                                                                           v0
                                                                                           v1
                                                                                           v2
                                                                                           v3
                                                                                           v4
                                                                                           v5
                                                                                           v6
                                                                                           v9
                                                                                           v14)
                                                                                        (coe
                                                                                           MAlonzo.Code.Algebra.RingSolver.Lemmas.du36
                                                                                           v4
                                                                                           (coe
                                                                                              MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                              v4
                                                                                              (coe
                                                                                                 MAlonzo.Code.Algebra.RingSolver.Lemmas.du88
                                                                                                 v4)
                                                                                              v13)
                                                                                           (coe
                                                                                              du368
                                                                                              v0
                                                                                              v1
                                                                                              v2
                                                                                              v3
                                                                                              v4
                                                                                              v5
                                                                                              v6
                                                                                              v9
                                                                                              v14))
                                                                                        (coe du54 v4
                                                                                           (coe du52
                                                                                              v4
                                                                                              (coe
                                                                                                 du106
                                                                                                 v4)
                                                                                              v13)
                                                                                           (coe
                                                                                              du368
                                                                                              v0
                                                                                              v1
                                                                                              v2
                                                                                              v3
                                                                                              v4
                                                                                              v5
                                                                                              v6
                                                                                              v9
                                                                                              v14))
                                                                                        (coe
                                                                                           MAlonzo.Code.Function.du158
                                                                                           (coe
                                                                                              du144
                                                                                              v4
                                                                                              (coe
                                                                                                 MAlonzo.Code.Algebra.RingSolver.Lemmas.du36
                                                                                                 v4
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                                    v4
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Algebra.RingSolver.Lemmas.du88
                                                                                                       v4)
                                                                                                    v13)
                                                                                                 (coe
                                                                                                    du368
                                                                                                    v0
                                                                                                    v1
                                                                                                    v2
                                                                                                    v3
                                                                                                    v4
                                                                                                    v5
                                                                                                    v6
                                                                                                    v9
                                                                                                    v14))
                                                                                              (coe
                                                                                                 du368
                                                                                                 v0
                                                                                                 v1
                                                                                                 v2
                                                                                                 v3
                                                                                                 v4
                                                                                                 v5
                                                                                                 v6
                                                                                                 v9
                                                                                                 v14))
                                                                                           (coe du32
                                                                                              v4
                                                                                              (coe
                                                                                                 du368
                                                                                                 v0
                                                                                                 v1
                                                                                                 v2
                                                                                                 v3
                                                                                                 v4
                                                                                                 v5
                                                                                                 v6
                                                                                                 v9
                                                                                                 v14)
                                                                                              v13))
                                                                                        (coe du242
                                                                                           v4
                                                                                           (coe du54
                                                                                              v4
                                                                                              (coe
                                                                                                 du52
                                                                                                 v4
                                                                                                 (coe
                                                                                                    du106
                                                                                                    v4)
                                                                                                 v13)
                                                                                              (coe
                                                                                                 du368
                                                                                                 v0
                                                                                                 v1
                                                                                                 v2
                                                                                                 v3
                                                                                                 v4
                                                                                                 v5
                                                                                                 v6
                                                                                                 v9
                                                                                                 v14)))))
                                                                       MAlonzo.Code.Relation.Nullary.C26
                                                                         v16 -> coe du136 v4
                                                                                  (coe d364 v0 v1 v2
                                                                                     v3
                                                                                     v4
                                                                                     v5
                                                                                     v6
                                                                                     v7
                                                                                     (coe C354 v7
                                                                                        (coe C350
                                                                                           v7)
                                                                                        v9)
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                        v7
                                                                                        v13
                                                                                        v14))
                                                                       _ -> coe
                                                                              MAlonzo.RTE.mazUnreachableError
                        _ -> coe MAlonzo.RTE.mazUnreachableError
        C354 v11 v12 v13 -> coe du136 v4
                              (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                 (coe d588 v0 v1 v2 v3 v4 v5 v6 v7 (coe C354 v7 v12 v13) v9)
                                 v10)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name896 = "Algebra.RingSolver.\8709*x+HN-homo"
d896 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = let v11 = coe du428 v0 v1 v2 v3 v4 v5 v6 v8 (coe du570 v3 v7) in
      case coe v11 of
          MAlonzo.Code.Relation.Nullary.C22 v12 -> coe d826 v0 v1 v2 v3 v4 v5
                                                     v6
                                                     v7
                                                     v8
                                                     v12
                                                     v10
          MAlonzo.Code.Relation.Nullary.C26 v12 -> coe du32 v4
                                                     (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
                                                     v9
          _ -> coe MAlonzo.RTE.mazUnreachableError
name932 = "Algebra.RingSolver.+H-homo"
d932 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v8 of
        C350 v11 -> coe du144 v4
                      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v4
                         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v4)
                         (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                            (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 (coe C350 v7) v9)
                            v10))
                      (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                         (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 (coe C350 v7) v9)
                         v10)
                      (coe MAlonzo.Code.Data.Product.d26 (coe du86 v4)
                         (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                            (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 (coe C350 v7) v9)
                            v10))
        C354 v11 v12 v13 -> case coe v9 of
                                C350 v14 -> coe du144 v4
                                              (coe
                                                 MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                 v4
                                                 (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                    (coe d612 v0 v1 v2 v3 v4 v5 v6 v7
                                                       (coe C354 v7 v12 v13)
                                                       (coe C350 v7))
                                                    v10)
                                                 (coe
                                                    MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                                                    v4))
                                              (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                 (coe d612 v0 v1 v2 v3 v4 v5 v6 v7
                                                    (coe C354 v7 v12 v13)
                                                    (coe C350 v7))
                                                 v10)
                                              (coe MAlonzo.Code.Data.Product.d28 (coe du86 v4)
                                                 (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                    (coe d612 v0 v1 v2 v3 v4 v5 v6 v7
                                                       (coe C354 v7 v12 v13)
                                                       (coe C350 v7))
                                                    v10))
                                C354 v14 v15 v16 -> case coe v10 of
                                                        MAlonzo.Code.Data.Vec.C22 v17 v18 v19 -> coe
                                                                                                   MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                                                                   (coe
                                                                                                      du244
                                                                                                      v4
                                                                                                      (coe
                                                                                                         d364
                                                                                                         v0
                                                                                                         v1
                                                                                                         v2
                                                                                                         v3
                                                                                                         v4
                                                                                                         v5
                                                                                                         v6
                                                                                                         v7
                                                                                                         (coe
                                                                                                            d588
                                                                                                            v0
                                                                                                            v1
                                                                                                            v2
                                                                                                            v3
                                                                                                            v4
                                                                                                            v5
                                                                                                            v6
                                                                                                            v7
                                                                                                            (coe
                                                                                                               d612
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v7
                                                                                                               v12
                                                                                                               v15)
                                                                                                            (coe
                                                                                                               du616
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v13
                                                                                                               v16))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Vec.C22
                                                                                                            v7
                                                                                                            v18
                                                                                                            v19))
                                                                                                      (coe
                                                                                                         d364
                                                                                                         v0
                                                                                                         v1
                                                                                                         v2
                                                                                                         v3
                                                                                                         v4
                                                                                                         v5
                                                                                                         v6
                                                                                                         v7
                                                                                                         (coe
                                                                                                            C354
                                                                                                            v7
                                                                                                            (coe
                                                                                                               d612
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v7
                                                                                                               v12
                                                                                                               v15)
                                                                                                            (coe
                                                                                                               du616
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v13
                                                                                                               v16))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Vec.C22
                                                                                                            v7
                                                                                                            v18
                                                                                                            v19))
                                                                                                      (coe
                                                                                                         du54
                                                                                                         v4
                                                                                                         (coe
                                                                                                            du54
                                                                                                            v4
                                                                                                            (coe
                                                                                                               du52
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  d364
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v12
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                                     v7
                                                                                                                     v18
                                                                                                                     v19))
                                                                                                               v18)
                                                                                                            (coe
                                                                                                               du368
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v13
                                                                                                               v19))
                                                                                                         (coe
                                                                                                            du54
                                                                                                            v4
                                                                                                            (coe
                                                                                                               du52
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  d364
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v15
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                                     v7
                                                                                                                     v18
                                                                                                                     v19))
                                                                                                               v18)
                                                                                                            (coe
                                                                                                               du368
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v16
                                                                                                               v19)))
                                                                                                      (coe
                                                                                                         d852
                                                                                                         v0
                                                                                                         v1
                                                                                                         v2
                                                                                                         v3
                                                                                                         v4
                                                                                                         v5
                                                                                                         v6
                                                                                                         v7
                                                                                                         (coe
                                                                                                            d612
                                                                                                            v0
                                                                                                            v1
                                                                                                            v2
                                                                                                            v3
                                                                                                            v4
                                                                                                            v5
                                                                                                            v6
                                                                                                            v7
                                                                                                            v12
                                                                                                            v15)
                                                                                                         (coe
                                                                                                            du616
                                                                                                            v0
                                                                                                            v1
                                                                                                            v2
                                                                                                            v3
                                                                                                            v4
                                                                                                            v5
                                                                                                            v6
                                                                                                            v13
                                                                                                            v16)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Vec.C22
                                                                                                            v7
                                                                                                            v18
                                                                                                            v19))
                                                                                                      (coe
                                                                                                         du244
                                                                                                         v4
                                                                                                         (coe
                                                                                                            du54
                                                                                                            v4
                                                                                                            (coe
                                                                                                               du52
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  d364
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  (coe
                                                                                                                     d612
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v12
                                                                                                                     v15)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                                     v7
                                                                                                                     v18
                                                                                                                     v19))
                                                                                                               v18)
                                                                                                            (coe
                                                                                                               du368
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               (coe
                                                                                                                  du616
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v13
                                                                                                                  v16)
                                                                                                               v19))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                            v4
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du54
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v12
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19))
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v15
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19)))
                                                                                                               v18)
                                                                                                            (coe
                                                                                                               du54
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v13
                                                                                                                  v19)
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v16
                                                                                                                  v19)))
                                                                                                         (coe
                                                                                                            du54
                                                                                                            v4
                                                                                                            (coe
                                                                                                               du54
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du52
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v12
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v13
                                                                                                                  v19))
                                                                                                            (coe
                                                                                                               du54
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du52
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v15
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v16
                                                                                                                  v19)))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Function.du176
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Function.du176
                                                                                                               (coe
                                                                                                                  d932
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v12
                                                                                                                  v15
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                                     v7
                                                                                                                     v18
                                                                                                                     v19))
                                                                                                               (coe
                                                                                                                  du64
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     (coe
                                                                                                                        d612
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        v15)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19))
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v15
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19)))
                                                                                                                  v18
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du136
                                                                                                                  v4
                                                                                                                  v18))
                                                                                                            (coe
                                                                                                               du84
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     (coe
                                                                                                                        d612
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        v15)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v15
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19)))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  (coe
                                                                                                                     du616
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v13
                                                                                                                     v16)
                                                                                                                  v19)
                                                                                                               (coe
                                                                                                                  du54
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v13
                                                                                                                     v19)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v16
                                                                                                                     v19)))
                                                                                                            (coe
                                                                                                               du942
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v13
                                                                                                               v16
                                                                                                               v19))
                                                                                                         (coe
                                                                                                            du244
                                                                                                            v4
                                                                                                            (coe
                                                                                                               du54
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du52
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v15
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19)))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du54
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v13
                                                                                                                     v19)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v16
                                                                                                                     v19)))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Algebra.RingSolver.Lemmas.du36
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Algebra.RingSolver.Lemmas.du36
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v13
                                                                                                                     v19))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Algebra.RingSolver.Lemmas.du36
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v15
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v16
                                                                                                                     v19)))
                                                                                                            (coe
                                                                                                               du54
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du54
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v13
                                                                                                                     v19))
                                                                                                               (coe
                                                                                                                  du54
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v15
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v16
                                                                                                                     v19)))
                                                                                                            (coe
                                                                                                               du22
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  d364
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v12
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                                     v7
                                                                                                                     v18
                                                                                                                     v19))
                                                                                                               (coe
                                                                                                                  d364
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v15
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                                     v7
                                                                                                                     v18
                                                                                                                     v19))
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v13
                                                                                                                  v19)
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v16
                                                                                                                  v19)
                                                                                                               v18)
                                                                                                            (coe
                                                                                                               du242
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du54
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v12
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v13
                                                                                                                        v19))
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v15
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v16
                                                                                                                        v19)))))))
                                                        _ -> coe MAlonzo.RTE.mazUnreachableError
                                _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name942 = "Algebra.RingSolver.+N-homo"
d942 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du942 v0 v1 v2 v3 v4 v5 v6 v8 v9 v10
du942 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v7 of
        C356 v10 -> case coe v8 of
                        C356 v11 -> coe du202 v5 v10 v11
                        _ -> coe MAlonzo.RTE.mazUnreachableError
        C360 v10 v11 -> case coe v8 of
                            C360 v12 v13 -> coe d932 v0 v1 v2 v3 v4 v5 v6 v10 v11 v13 v9
                            _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name947 = "Algebra.RingSolver..absurdlambda"
d947 = erased
name986 = "Algebra.RingSolver.*x+H-homo"
d986 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = let v12
          = case coe v9 of
                C354 v12 v13 v14 -> coe
                                      MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                      (coe du244 v4
                                         (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                            (coe d588 v0 v1 v2 v3 v4 v5 v6 v7
                                               (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v13)
                                               v14)
                                            (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                         (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                            (coe C354 v7 (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v13)
                                               v14)
                                            (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                         (coe du54 v4
                                            (coe du52 v4
                                               (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                  (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                               v10)
                                            (coe du54 v4
                                               (coe du52 v4
                                                  (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v13
                                                     (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                  v10)
                                               (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11)))
                                         (coe d852 v0 v1 v2 v3 v4 v5 v6 v7
                                            (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v13)
                                            v14
                                            (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                         (coe du244 v4
                                            (coe du54 v4
                                               (coe du52 v4
                                                  (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                     (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v13)
                                                     (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                  v10)
                                               (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11))
                                            (coe
                                               MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                               v4
                                               (coe
                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                  v4
                                                  (coe du54 v4
                                                     (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                        (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                     (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v13
                                                        (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11)))
                                                  v10)
                                               (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11))
                                            (coe du54 v4
                                               (coe du52 v4
                                                  (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                     (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                  v10)
                                               (coe du54 v4
                                                  (coe du52 v4
                                                     (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v13
                                                        (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                     v10)
                                                  (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11)))
                                            (coe MAlonzo.Code.Function.du176
                                               (coe MAlonzo.Code.Function.du176
                                                  (coe d932 v0 v1 v2 v3 v4 v5 v6 v7 v8 v13
                                                     (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                  (coe du64 v4
                                                     (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                        (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v13)
                                                        (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                     (coe du54 v4
                                                        (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                           (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                              v11))
                                                        (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v13
                                                           (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                              v11)))
                                                     v10
                                                     v10)
                                                  (coe du136 v4 v10))
                                               (coe du84 v4
                                                  (coe
                                                     MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                     v4
                                                     (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                        (coe d612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v13)
                                                        (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                     v10)
                                                  (coe
                                                     MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                     v4
                                                     (coe du54 v4
                                                        (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                           (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                              v11))
                                                        (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v13
                                                           (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                              v11)))
                                                     v10)
                                                  (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11)
                                                  (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11))
                                               (coe du136 v4
                                                  (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11)))
                                            (coe du244 v4
                                               (coe du54 v4
                                                  (coe du52 v4
                                                     (coe du54 v4
                                                        (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                           (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                              v11))
                                                        (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v13
                                                           (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                              v11)))
                                                     v10)
                                                  (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11))
                                               (coe MAlonzo.Code.Algebra.RingSolver.Lemmas.du36 v4
                                                  (coe MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                     v4
                                                     (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                        (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                     v10)
                                                  (coe MAlonzo.Code.Algebra.RingSolver.Lemmas.du36
                                                     v4
                                                     (coe
                                                        MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                        v4
                                                        (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v13
                                                           (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                              v11))
                                                        v10)
                                                     (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11)))
                                               (coe du54 v4
                                                  (coe du52 v4
                                                     (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                        (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                     v10)
                                                  (coe du54 v4
                                                     (coe du52 v4
                                                        (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v13
                                                           (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                              v11))
                                                        v10)
                                                     (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11)))
                                               (coe du20 v4
                                                  (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                     (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                  (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v13
                                                     (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                                  (coe du368 v0 v1 v2 v3 v4 v5 v6 v14 v11)
                                                  v10)
                                               (coe du242 v4
                                                  (coe du54 v4
                                                     (coe du52 v4
                                                        (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                           (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                              v11))
                                                        v10)
                                                     (coe du54 v4
                                                        (coe du52 v4
                                                           (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v13
                                                              (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                                 v11))
                                                           v10)
                                                        (coe du368 v0 v1 v2 v3 v4 v5 v6 v14
                                                           v11)))))))
                _ -> coe MAlonzo.RTE.mazUnreachableError
      in
      case coe v8 of
          C350 v13 -> case coe v9 of
                          C350 v14 -> coe MAlonzo.Code.Function.du158
                                        (coe du144 v4
                                           (coe MAlonzo.Code.Algebra.RingSolver.Lemmas.du36 v4
                                              (coe MAlonzo.Code.Algebra.RingSolver.Lemmas.du34 v4
                                                 (coe MAlonzo.Code.Algebra.RingSolver.Lemmas.du88
                                                    v4)
                                                 v10)
                                              (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                 (coe d640 v0 v1 v2 v3 v4 v5 v6 v7 (coe C350 v7)
                                                    (coe C350 v7))
                                                 (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11)))
                                           (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                              (coe d640 v0 v1 v2 v3 v4 v5 v6 v7 (coe C350 v7)
                                                 (coe C350 v7))
                                              (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11)))
                                        (coe du32 v4
                                           (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                              (coe d640 v0 v1 v2 v3 v4 v5 v6 v7 (coe C350 v7)
                                                 (coe C350 v7))
                                              (coe MAlonzo.Code.Data.Vec.C22 v7 v10 v11))
                                           v10)
                          _ -> coe v12
          C354 v13 v14 v15 -> case coe v9 of
                                  C350 v16 -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                (coe du244 v4
                                                   (coe du54 v4
                                                      (coe du52 v4
                                                         (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                            (coe C354 v7 v14 v15)
                                                            (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                               v11))
                                                         v10)
                                                      (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                         (coe du570 v3 v7)
                                                         v11))
                                                   (coe
                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                      v4
                                                      (coe du52 v4
                                                         (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                            (coe C354 v7 v14 v15)
                                                            (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                               v11))
                                                         v10)
                                                      (coe du106 v4))
                                                   (coe du54 v4
                                                      (coe du52 v4
                                                         (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                            (coe C354 v7 v14 v15)
                                                            (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                               v11))
                                                         v10)
                                                      (coe du106 v4))
                                                   (coe MAlonzo.Code.Function.du176
                                                      (coe du136 v4
                                                         (coe du52 v4
                                                            (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                               (coe C354 v7 v14 v15)
                                                               (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                                  v11))
                                                            v10))
                                                      (coe du84 v4
                                                         (coe du52 v4
                                                            (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                               (coe C354 v7 v14 v15)
                                                               (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                                  v11))
                                                            v10)
                                                         (coe du52 v4
                                                            (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                               (coe C354 v7 v14 v15)
                                                               (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                                  v11))
                                                            v10)
                                                         (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                            (coe du570 v3 v7)
                                                            v11)
                                                         (coe du106 v4))
                                                      (coe du814 v0 v1 v2 v3 v4 v5 v6 v11))
                                                   (coe du242 v4
                                                      (coe du54 v4
                                                         (coe du52 v4
                                                            (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                               (coe C354 v7 v14 v15)
                                                               (coe MAlonzo.Code.Data.Vec.C22 v7 v10
                                                                  v11))
                                                            v10)
                                                         (coe du106 v4))))
                                  _ -> coe v12
          _ -> coe v12
name1016 = "Algebra.RingSolver.*NH-homo"
d1016 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v9 of
        C350 v12 -> coe du144 v4
                      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v4
                         (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v11)
                         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                            v4))
                      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v4)
                      (coe MAlonzo.Code.Data.Product.d28 (coe du148 v4)
                         (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v11))
        C354 v12 v13 v14 -> let v15
                                  = coe du428 v0 v1 v2 v3 v4 v5 v6 v8 (coe du570 v3 v7)
                              in
                              case coe v15 of
                                  MAlonzo.Code.Relation.Nullary.C22 v16 -> coe
                                                                             MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                                             (coe du244 v4
                                                                                (coe du106 v4)
                                                                                (coe
                                                                                   MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                   v4
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                                                                                      v4)
                                                                                   (coe du54 v4
                                                                                      (coe du52 v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            v13
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         v10)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v11)))
                                                                                (coe du52 v4
                                                                                   (coe du368 v0 v1
                                                                                      v2
                                                                                      v3
                                                                                      v4
                                                                                      v5
                                                                                      v6
                                                                                      v8
                                                                                      v11)
                                                                                   (coe du54 v4
                                                                                      (coe du52 v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            v13
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         v10)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v11)))
                                                                                (coe du144 v4
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                      v4
                                                                                      (coe
                                                                                         MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                                                                                         v4)
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                                                                                      v4)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Product.d26
                                                                                      (coe du148 v4)
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11))))
                                                                                (coe du244 v4
                                                                                   (coe du52 v4
                                                                                      (coe du106 v4)
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                      v4
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v8
                                                                                         v11)
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11)))
                                                                                   (coe du52 v4
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v8
                                                                                         v11)
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Function.du176
                                                                                      (coe d826 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v7
                                                                                         v8
                                                                                         v16
                                                                                         v11)
                                                                                      (coe du64 v4
                                                                                         (coe du106
                                                                                            v4)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v8
                                                                                            v11)
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  d364
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v13
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                     v7
                                                                                                     v10
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v14
                                                                                               v11))
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  d364
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v13
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                     v7
                                                                                                     v10
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v14
                                                                                               v11)))
                                                                                      (coe du136 v4
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  d364
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v13
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                     v7
                                                                                                     v10
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v14
                                                                                               v11))))
                                                                                   (coe du242 v4
                                                                                      (coe du52 v4
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v8
                                                                                            v11)
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  d364
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v13
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                     v7
                                                                                                     v10
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v14
                                                                                               v11))))))
                                  MAlonzo.Code.Relation.Nullary.C26 v16 -> coe
                                                                             MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                                             (coe du244 v4
                                                                                (coe du54 v4
                                                                                   (coe du52 v4
                                                                                      (coe d364 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v7
                                                                                         (coe d654
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            v8
                                                                                            v13)
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Vec.C22
                                                                                            v7
                                                                                            v10
                                                                                            v11))
                                                                                      v10)
                                                                                   (coe du368 v0 v1
                                                                                      v2
                                                                                      v3
                                                                                      v4
                                                                                      v5
                                                                                      v6
                                                                                      (coe du666 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v8
                                                                                         v14)
                                                                                      v11))
                                                                                (coe
                                                                                   MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                   v4
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                      v4
                                                                                      (coe du52 v4
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v8
                                                                                            v11)
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            v13
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11)))
                                                                                      v10)
                                                                                   (coe du52 v4
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v8
                                                                                         v11)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v11)))
                                                                                (coe du52 v4
                                                                                   (coe du368 v0 v1
                                                                                      v2
                                                                                      v3
                                                                                      v4
                                                                                      v5
                                                                                      v6
                                                                                      v8
                                                                                      v11)
                                                                                   (coe du54 v4
                                                                                      (coe du52 v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            v13
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         v10)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v11)))
                                                                                (coe
                                                                                   MAlonzo.Code.Function.du176
                                                                                   (coe
                                                                                      MAlonzo.Code.Function.du176
                                                                                      (coe d1016 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v7
                                                                                         v8
                                                                                         v13
                                                                                         v10
                                                                                         v11)
                                                                                      (coe du64 v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            (coe
                                                                                               d654
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v8
                                                                                               v13)
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v8
                                                                                               v11)
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11)))
                                                                                         v10
                                                                                         v10)
                                                                                      (coe du136 v4
                                                                                         v10))
                                                                                   (coe du84 v4
                                                                                      (coe
                                                                                         MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                         v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            (coe
                                                                                               d654
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v8
                                                                                               v13)
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         v10)
                                                                                      (coe
                                                                                         MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                         v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v8
                                                                                               v11)
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11)))
                                                                                         v10)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         (coe du666
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v8
                                                                                            v14)
                                                                                         v11)
                                                                                      (coe du52 v4
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v8
                                                                                            v11)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11)))
                                                                                   (coe du1048 v0 v1
                                                                                      v2
                                                                                      v3
                                                                                      v4
                                                                                      v5
                                                                                      v6
                                                                                      v8
                                                                                      v14
                                                                                      v11))
                                                                                (coe du244 v4
                                                                                   (coe du54 v4
                                                                                      (coe du52 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v8
                                                                                               v11)
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11)))
                                                                                         v10)
                                                                                      (coe du52 v4
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v8
                                                                                            v11)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                      v4
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v8
                                                                                         v11)
                                                                                      (coe
                                                                                         MAlonzo.Code.Algebra.RingSolver.Lemmas.du36
                                                                                         v4
                                                                                         (coe
                                                                                            MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11)))
                                                                                   (coe du52 v4
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v8
                                                                                         v11)
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11)))
                                                                                   (coe du26 v4
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v8
                                                                                         v11)
                                                                                      (coe d364 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v7
                                                                                         v13
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Vec.C22
                                                                                            v7
                                                                                            v10
                                                                                            v11))
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v11)
                                                                                      v10)
                                                                                   (coe du242 v4
                                                                                      (coe du52 v4
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v8
                                                                                            v11)
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  d364
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v13
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                     v7
                                                                                                     v10
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v14
                                                                                               v11))))))
                                  _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1028 = "Algebra.RingSolver.*HN-homo"
d1028 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v8 of
        C350 v12 -> coe du144 v4
                      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v4
                         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v4)
                         (coe du368 v0 v1 v2 v3 v4 v5 v6 v9 v11))
                      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v4)
                      (coe MAlonzo.Code.Data.Product.d26 (coe du148 v4)
                         (coe du368 v0 v1 v2 v3 v4 v5 v6 v9 v11))
        C354 v12 v13 v14 -> let v15
                                  = coe du428 v0 v1 v2 v3 v4 v5 v6 v9 (coe du570 v3 v7)
                              in
                              case coe v15 of
                                  MAlonzo.Code.Relation.Nullary.C22 v16 -> coe
                                                                             MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                                             (coe du244 v4
                                                                                (coe du106 v4)
                                                                                (coe
                                                                                   MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                   v4
                                                                                   (coe du54 v4
                                                                                      (coe du52 v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            v13
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         v10)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v11))
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                                                                                      v4))
                                                                                (coe du52 v4
                                                                                   (coe du54 v4
                                                                                      (coe du52 v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            v13
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         v10)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v11))
                                                                                   (coe du368 v0 v1
                                                                                      v2
                                                                                      v3
                                                                                      v4
                                                                                      v5
                                                                                      v6
                                                                                      v9
                                                                                      v11))
                                                                                (coe du144 v4
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                      v4
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11))
                                                                                      (coe
                                                                                         MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                                                                                         v4))
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                                                                                      v4)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Product.d28
                                                                                      (coe du148 v4)
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11))))
                                                                                (coe du244 v4
                                                                                   (coe du52 v4
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11))
                                                                                      (coe du106
                                                                                         v4))
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                      v4
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11))
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v9
                                                                                         v11))
                                                                                   (coe du52 v4
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11))
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v9
                                                                                         v11))
                                                                                   (coe
                                                                                      MAlonzo.Code.Function.du176
                                                                                      (coe du136 v4
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  d364
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v13
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                     v7
                                                                                                     v10
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v14
                                                                                               v11)))
                                                                                      (coe du64 v4
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  d364
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v13
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                     v7
                                                                                                     v10
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v14
                                                                                               v11))
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  d364
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v13
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                     v7
                                                                                                     v10
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v14
                                                                                               v11))
                                                                                         (coe du106
                                                                                            v4)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v9
                                                                                            v11))
                                                                                      (coe d826 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v7
                                                                                         v9
                                                                                         v16
                                                                                         v11))
                                                                                   (coe du242 v4
                                                                                      (coe du52 v4
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  d364
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v13
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                     v7
                                                                                                     v10
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v14
                                                                                               v11))
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v9
                                                                                            v11)))))
                                  MAlonzo.Code.Relation.Nullary.C26 v16 -> coe
                                                                             MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                                             (coe du244 v4
                                                                                (coe du54 v4
                                                                                   (coe du52 v4
                                                                                      (coe d364 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v7
                                                                                         (coe d658
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            v13
                                                                                            v9)
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Vec.C22
                                                                                            v7
                                                                                            v10
                                                                                            v11))
                                                                                      v10)
                                                                                   (coe du368 v0 v1
                                                                                      v2
                                                                                      v3
                                                                                      v4
                                                                                      v5
                                                                                      v6
                                                                                      (coe du666 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v9)
                                                                                      v11))
                                                                                (coe
                                                                                   MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                   v4
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                      v4
                                                                                      (coe du52 v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            v13
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v9
                                                                                            v11))
                                                                                      v10)
                                                                                   (coe du52 v4
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v11)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v9
                                                                                         v11)))
                                                                                (coe du52 v4
                                                                                   (coe du54 v4
                                                                                      (coe du52 v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            v13
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         v10)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v11))
                                                                                   (coe du368 v0 v1
                                                                                      v2
                                                                                      v3
                                                                                      v4
                                                                                      v5
                                                                                      v6
                                                                                      v9
                                                                                      v11))
                                                                                (coe
                                                                                   MAlonzo.Code.Function.du176
                                                                                   (coe
                                                                                      MAlonzo.Code.Function.du176
                                                                                      (coe d1028 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v7
                                                                                         v13
                                                                                         v9
                                                                                         v10
                                                                                         v11)
                                                                                      (coe du64 v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            (coe
                                                                                               d658
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               v9)
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v9
                                                                                               v11))
                                                                                         v10
                                                                                         v10)
                                                                                      (coe du136 v4
                                                                                         v10))
                                                                                   (coe du84 v4
                                                                                      (coe
                                                                                         MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                         v4
                                                                                         (coe d364
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v7
                                                                                            (coe
                                                                                               d658
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               v9)
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.C22
                                                                                               v7
                                                                                               v10
                                                                                               v11))
                                                                                         v10)
                                                                                      (coe
                                                                                         MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                         v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v9
                                                                                               v11))
                                                                                         v10)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         (coe du666
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v9)
                                                                                         v11)
                                                                                      (coe du52 v4
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v9
                                                                                            v11)))
                                                                                   (coe du1048 v0 v1
                                                                                      v2
                                                                                      v3
                                                                                      v4
                                                                                      v5
                                                                                      v6
                                                                                      v14
                                                                                      v9
                                                                                      v11))
                                                                                (coe du244 v4
                                                                                   (coe du54 v4
                                                                                      (coe du52 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v9
                                                                                               v11))
                                                                                         v10)
                                                                                      (coe du52 v4
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v9
                                                                                            v11)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                      v4
                                                                                      (coe
                                                                                         MAlonzo.Code.Algebra.RingSolver.Lemmas.du36
                                                                                         v4
                                                                                         (coe
                                                                                            MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11))
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v9
                                                                                         v11))
                                                                                   (coe du52 v4
                                                                                      (coe du54 v4
                                                                                         (coe du52
                                                                                            v4
                                                                                            (coe
                                                                                               d364
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v7
                                                                                               v13
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Vec.C22
                                                                                                  v7
                                                                                                  v10
                                                                                                  v11))
                                                                                            v10)
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v14
                                                                                            v11))
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v9
                                                                                         v11))
                                                                                   (coe du24 v4
                                                                                      (coe d364 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v7
                                                                                         v13
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Vec.C22
                                                                                            v7
                                                                                            v10
                                                                                            v11))
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v14
                                                                                         v11)
                                                                                      (coe du368 v0
                                                                                         v1
                                                                                         v2
                                                                                         v3
                                                                                         v4
                                                                                         v5
                                                                                         v6
                                                                                         v9
                                                                                         v11)
                                                                                      v10)
                                                                                   (coe du242 v4
                                                                                      (coe du52 v4
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  d364
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  v7
                                                                                                  v13
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                     v7
                                                                                                     v10
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v14
                                                                                               v11))
                                                                                         (coe du368
                                                                                            v0
                                                                                            v1
                                                                                            v2
                                                                                            v3
                                                                                            v4
                                                                                            v5
                                                                                            v6
                                                                                            v9
                                                                                            v11)))))
                                  _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1038 = "Algebra.RingSolver.*H-homo"
d1038 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v8 of
        C350 v11 -> coe MAlonzo.Code.Function.du158
                      (coe du144 v4
                         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v4
                            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v4)
                            (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v9 v10))
                         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                            v4))
                      (coe MAlonzo.Code.Data.Product.d26 (coe du148 v4)
                         (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v9 v10))
        C354 v11 v12 v13 -> case coe v9 of
                                C350 v14 -> coe MAlonzo.Code.Function.du158
                                              (coe du144 v4
                                                 (coe
                                                    MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                    v4
                                                    (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                       (coe C354 v7 v12 v13)
                                                       v10)
                                                    (coe
                                                       MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                                                       v4))
                                                 (coe
                                                    MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170
                                                    v4))
                                              (coe MAlonzo.Code.Data.Product.d28 (coe du148 v4)
                                                 (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                    (coe C354 v7 v12 v13)
                                                    v10))
                                C354 v14 v15 v16 -> case coe v10 of
                                                        MAlonzo.Code.Data.Vec.C22 v17 v18 v19 -> coe
                                                                                                   MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                                                                   (coe
                                                                                                      du244
                                                                                                      v4
                                                                                                      (coe
                                                                                                         d364
                                                                                                         v0
                                                                                                         v1
                                                                                                         v2
                                                                                                         v3
                                                                                                         v4
                                                                                                         v5
                                                                                                         v6
                                                                                                         v7
                                                                                                         (coe
                                                                                                            d588
                                                                                                            v0
                                                                                                            v1
                                                                                                            v2
                                                                                                            v3
                                                                                                            v4
                                                                                                            v5
                                                                                                            v6
                                                                                                            v7
                                                                                                            (coe
                                                                                                               d640
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v7
                                                                                                               (coe
                                                                                                                  d662
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v12
                                                                                                                  v15)
                                                                                                               (coe
                                                                                                                  d612
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  (coe
                                                                                                                     d658
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v12
                                                                                                                     v16)
                                                                                                                  (coe
                                                                                                                     d654
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v13
                                                                                                                     v15)))
                                                                                                            (coe
                                                                                                               du666
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v13
                                                                                                               v16))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Vec.C22
                                                                                                            v7
                                                                                                            v18
                                                                                                            v19))
                                                                                                      (coe
                                                                                                         d364
                                                                                                         v0
                                                                                                         v1
                                                                                                         v2
                                                                                                         v3
                                                                                                         v4
                                                                                                         v5
                                                                                                         v6
                                                                                                         v7
                                                                                                         (coe
                                                                                                            C354
                                                                                                            v7
                                                                                                            (coe
                                                                                                               d640
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v7
                                                                                                               (coe
                                                                                                                  d662
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v12
                                                                                                                  v15)
                                                                                                               (coe
                                                                                                                  d612
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  (coe
                                                                                                                     d658
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v12
                                                                                                                     v16)
                                                                                                                  (coe
                                                                                                                     d654
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v13
                                                                                                                     v15)))
                                                                                                            (coe
                                                                                                               du666
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v13
                                                                                                               v16))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Vec.C22
                                                                                                            v7
                                                                                                            v18
                                                                                                            v19))
                                                                                                      (coe
                                                                                                         du52
                                                                                                         v4
                                                                                                         (coe
                                                                                                            du54
                                                                                                            v4
                                                                                                            (coe
                                                                                                               du52
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  d364
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v12
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                                     v7
                                                                                                                     v18
                                                                                                                     v19))
                                                                                                               v18)
                                                                                                            (coe
                                                                                                               du368
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v13
                                                                                                               v19))
                                                                                                         (coe
                                                                                                            du54
                                                                                                            v4
                                                                                                            (coe
                                                                                                               du52
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  d364
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v15
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                                     v7
                                                                                                                     v18
                                                                                                                     v19))
                                                                                                               v18)
                                                                                                            (coe
                                                                                                               du368
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v16
                                                                                                               v19)))
                                                                                                      (coe
                                                                                                         d852
                                                                                                         v0
                                                                                                         v1
                                                                                                         v2
                                                                                                         v3
                                                                                                         v4
                                                                                                         v5
                                                                                                         v6
                                                                                                         v7
                                                                                                         (coe
                                                                                                            d640
                                                                                                            v0
                                                                                                            v1
                                                                                                            v2
                                                                                                            v3
                                                                                                            v4
                                                                                                            v5
                                                                                                            v6
                                                                                                            v7
                                                                                                            (coe
                                                                                                               d662
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v7
                                                                                                               v12
                                                                                                               v15)
                                                                                                            (coe
                                                                                                               d612
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v7
                                                                                                               (coe
                                                                                                                  d658
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v12
                                                                                                                  v16)
                                                                                                               (coe
                                                                                                                  d654
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  v13
                                                                                                                  v15)))
                                                                                                         (coe
                                                                                                            du666
                                                                                                            v0
                                                                                                            v1
                                                                                                            v2
                                                                                                            v3
                                                                                                            v4
                                                                                                            v5
                                                                                                            v6
                                                                                                            v13
                                                                                                            v16)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Vec.C22
                                                                                                            v7
                                                                                                            v18
                                                                                                            v19))
                                                                                                      (coe
                                                                                                         du244
                                                                                                         v4
                                                                                                         (coe
                                                                                                            du54
                                                                                                            v4
                                                                                                            (coe
                                                                                                               du52
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  d364
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  (coe
                                                                                                                     d640
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     (coe
                                                                                                                        d662
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        v15)
                                                                                                                     (coe
                                                                                                                        d612
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        (coe
                                                                                                                           d658
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v12
                                                                                                                           v16)
                                                                                                                        (coe
                                                                                                                           d654
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v13
                                                                                                                           v15)))
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Vec.C22
                                                                                                                     v7
                                                                                                                     v18
                                                                                                                     v19))
                                                                                                               v18)
                                                                                                            (coe
                                                                                                               du368
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               (coe
                                                                                                                  du666
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v13
                                                                                                                  v16)
                                                                                                               v19))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                            v4
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du54
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        (coe
                                                                                                                           d662
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v12
                                                                                                                           v15)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     (coe
                                                                                                                        d612
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        (coe
                                                                                                                           d658
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v12
                                                                                                                           v16)
                                                                                                                        (coe
                                                                                                                           d654
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v13
                                                                                                                           v15))
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19)))
                                                                                                               v18)
                                                                                                            (coe
                                                                                                               du52
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v13
                                                                                                                  v19)
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v16
                                                                                                                  v19)))
                                                                                                         (coe
                                                                                                            du52
                                                                                                            v4
                                                                                                            (coe
                                                                                                               du54
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du52
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v12
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v13
                                                                                                                  v19))
                                                                                                            (coe
                                                                                                               du54
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du52
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v15
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v16
                                                                                                                  v19)))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Function.du176
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Function.du176
                                                                                                               (coe
                                                                                                                  d986
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  v7
                                                                                                                  (coe
                                                                                                                     d662
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     v12
                                                                                                                     v15)
                                                                                                                  (coe
                                                                                                                     d612
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     (coe
                                                                                                                        d658
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        v16)
                                                                                                                     (coe
                                                                                                                        d654
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v13
                                                                                                                        v15))
                                                                                                                  v18
                                                                                                                  v19)
                                                                                                               (coe
                                                                                                                  du64
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     (coe
                                                                                                                        d640
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        (coe
                                                                                                                           d662
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v12
                                                                                                                           v15)
                                                                                                                        (coe
                                                                                                                           d612
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d658
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              v16)
                                                                                                                           (coe
                                                                                                                              d654
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v13
                                                                                                                              v15)))
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19))
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d662
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              v15)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        (coe
                                                                                                                           d612
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d658
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              v16)
                                                                                                                           (coe
                                                                                                                              d654
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v13
                                                                                                                              v15))
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19)))
                                                                                                                  v18
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du136
                                                                                                                  v4
                                                                                                                  v18))
                                                                                                            (coe
                                                                                                               du84
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     d364
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v7
                                                                                                                     (coe
                                                                                                                        d640
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        (coe
                                                                                                                           d662
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v12
                                                                                                                           v15)
                                                                                                                        (coe
                                                                                                                           d612
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d658
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              v16)
                                                                                                                           (coe
                                                                                                                              d654
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v13
                                                                                                                              v15)))
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Vec.C22
                                                                                                                        v7
                                                                                                                        v18
                                                                                                                        v19))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d662
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              v15)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        (coe
                                                                                                                           d612
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d658
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              v16)
                                                                                                                           (coe
                                                                                                                              d654
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v13
                                                                                                                              v15))
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19)))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du368
                                                                                                                  v0
                                                                                                                  v1
                                                                                                                  v2
                                                                                                                  v3
                                                                                                                  v4
                                                                                                                  v5
                                                                                                                  v6
                                                                                                                  (coe
                                                                                                                     du666
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v13
                                                                                                                     v16)
                                                                                                                  v19)
                                                                                                               (coe
                                                                                                                  du52
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v13
                                                                                                                     v19)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v16
                                                                                                                     v19)))
                                                                                                            (coe
                                                                                                               du1048
                                                                                                               v0
                                                                                                               v1
                                                                                                               v2
                                                                                                               v3
                                                                                                               v4
                                                                                                               v5
                                                                                                               v6
                                                                                                               v13
                                                                                                               v16
                                                                                                               v19))
                                                                                                         (coe
                                                                                                            du244
                                                                                                            v4
                                                                                                            (coe
                                                                                                               du54
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du52
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d662
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              v15)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        (coe
                                                                                                                           d612
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d658
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              v16)
                                                                                                                           (coe
                                                                                                                              d654
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v13
                                                                                                                              v15))
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19)))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du52
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v13
                                                                                                                     v19)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v16
                                                                                                                     v19)))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du52
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v15
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19)))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        du54
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d658
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              v16)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d654
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v13
                                                                                                                              v15)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))))
                                                                                                                  v18)
                                                                                                               (coe
                                                                                                                  du52
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v13
                                                                                                                     v19)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v16
                                                                                                                     v19)))
                                                                                                            (coe
                                                                                                               du52
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du54
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v13
                                                                                                                     v19))
                                                                                                               (coe
                                                                                                                  du54
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v15
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du368
                                                                                                                     v0
                                                                                                                     v1
                                                                                                                     v2
                                                                                                                     v3
                                                                                                                     v4
                                                                                                                     v5
                                                                                                                     v6
                                                                                                                     v16
                                                                                                                     v19)))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Function.du176
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Function.du176
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Function.du176
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Function.du176
                                                                                                                        (coe
                                                                                                                           d1038
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v12
                                                                                                                           v15
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))
                                                                                                                        (coe
                                                                                                                           du64
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d662
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v15)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v15
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19)))
                                                                                                                           v18
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           du136
                                                                                                                           v4
                                                                                                                           v18))
                                                                                                                     (coe
                                                                                                                        du84
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d662
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v15)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v15
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19)))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d612
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d658
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v16)
                                                                                                                              (coe
                                                                                                                                 d654
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v13
                                                                                                                                 v15))
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))
                                                                                                                        (coe
                                                                                                                           du54
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d658
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v16)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d654
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v13
                                                                                                                                 v15)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))))
                                                                                                                     (coe
                                                                                                                        d932
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        (coe
                                                                                                                           d658
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v12
                                                                                                                           v16)
                                                                                                                        (coe
                                                                                                                           d654
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v13
                                                                                                                           v15)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19)))
                                                                                                                  (coe
                                                                                                                     du64
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d662
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v15)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d612
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d658
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v16)
                                                                                                                              (coe
                                                                                                                                 d654
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v13
                                                                                                                                 v15))
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19)))
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v15
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19)))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           du54
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d658
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v16)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d654
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v13
                                                                                                                                 v15)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))))
                                                                                                                     v18
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du136
                                                                                                                     v4
                                                                                                                     v18))
                                                                                                               (coe
                                                                                                                  du84
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d662
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v15)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           (coe
                                                                                                                              d612
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d658
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v16)
                                                                                                                              (coe
                                                                                                                                 d654
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v13
                                                                                                                                 v15))
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19)))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v15
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19)))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           du54
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d658
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v16)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d654
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v13
                                                                                                                                 v15)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v13
                                                                                                                        v19)
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v16
                                                                                                                        v19))
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v13
                                                                                                                        v19)
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v16
                                                                                                                        v19)))
                                                                                                               (coe
                                                                                                                  du136
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v13
                                                                                                                        v19)
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v16
                                                                                                                        v19))))
                                                                                                            (coe
                                                                                                               du244
                                                                                                               v4
                                                                                                               (coe
                                                                                                                  du54
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du54
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du52
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v15
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19)))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           du54
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d658
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 v16)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              (coe
                                                                                                                                 d654
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v13
                                                                                                                                 v15)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v13
                                                                                                                        v19)
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v16
                                                                                                                        v19)))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du52
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v15
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19)))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 du368
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v16
                                                                                                                                 v19))
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du368
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v13
                                                                                                                                 v19)
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v15
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19)))))
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v13
                                                                                                                        v19)
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v16
                                                                                                                        v19)))
                                                                                                               (coe
                                                                                                                  du52
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v12
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v13
                                                                                                                        v19))
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           d364
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v7
                                                                                                                           v15
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Vec.C22
                                                                                                                              v7
                                                                                                                              v18
                                                                                                                              v19))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v16
                                                                                                                        v19)))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Function.du176
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Function.du176
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Function.du176
                                                                                                                        (coe
                                                                                                                           du136
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))
                                                                                                                              v18))
                                                                                                                        (coe
                                                                                                                           du84
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 (coe
                                                                                                                                    d658
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    v16)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 (coe
                                                                                                                                    d654
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v13
                                                                                                                                    v15)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19)))
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    du368
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v16
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    du368
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v13
                                                                                                                                    v19)
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))))
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Function.du176
                                                                                                                           (coe
                                                                                                                              d1028
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              v16
                                                                                                                              v18
                                                                                                                              v19)
                                                                                                                           (coe
                                                                                                                              du84
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 (coe
                                                                                                                                    d658
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    v16)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    du368
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v16
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 (coe
                                                                                                                                    d654
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v13
                                                                                                                                    v15)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    du368
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v13
                                                                                                                                    v19)
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))))
                                                                                                                           (coe
                                                                                                                              d1016
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v13
                                                                                                                              v15
                                                                                                                              v18
                                                                                                                              v19)))
                                                                                                                     (coe
                                                                                                                        du64
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 (coe
                                                                                                                                    d658
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    v16)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 (coe
                                                                                                                                    d654
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v13
                                                                                                                                    v15)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))))
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    du368
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v16
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    du368
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v13
                                                                                                                                    v19)
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))))
                                                                                                                        v18
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        du136
                                                                                                                        v4
                                                                                                                        v18))
                                                                                                                  (coe
                                                                                                                     du84
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 (coe
                                                                                                                                    d658
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    v16)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 (coe
                                                                                                                                    d654
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v13
                                                                                                                                    v15)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    du368
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v16
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    du368
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v13
                                                                                                                                    v19)
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v13
                                                                                                                           v19)
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v16
                                                                                                                           v19))
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v13
                                                                                                                           v19)
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v16
                                                                                                                           v19)))
                                                                                                                  (coe
                                                                                                                     du136
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v13
                                                                                                                           v19)
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v16
                                                                                                                           v19))))
                                                                                                               (coe
                                                                                                                  du244
                                                                                                                  v4
                                                                                                                  (coe
                                                                                                                     du54
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du54
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              du54
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v12
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    du368
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v16
                                                                                                                                    v19))
                                                                                                                              (coe
                                                                                                                                 du52
                                                                                                                                 v4
                                                                                                                                 (coe
                                                                                                                                    du368
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v13
                                                                                                                                    v19)
                                                                                                                                 (coe
                                                                                                                                    d364
                                                                                                                                    v0
                                                                                                                                    v1
                                                                                                                                    v2
                                                                                                                                    v3
                                                                                                                                    v4
                                                                                                                                    v5
                                                                                                                                    v6
                                                                                                                                    v7
                                                                                                                                    v15
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Vec.C22
                                                                                                                                       v7
                                                                                                                                       v18
                                                                                                                                       v19)))))
                                                                                                                        v18)
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v13
                                                                                                                           v19)
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v16
                                                                                                                           v19)))
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Algebra.RingSolver.Lemmas.du36
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v13
                                                                                                                           v19))
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Algebra.RingSolver.Lemmas.du36
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Algebra.RingSolver.Lemmas.du34
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v15
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v16
                                                                                                                           v19)))
                                                                                                                  (coe
                                                                                                                     du52
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du54
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du52
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v12
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v13
                                                                                                                           v19))
                                                                                                                     (coe
                                                                                                                        du54
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du52
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              d364
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v7
                                                                                                                              v15
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Data.Vec.C22
                                                                                                                                 v7
                                                                                                                                 v18
                                                                                                                                 v19))
                                                                                                                           v18)
                                                                                                                        (coe
                                                                                                                           du368
                                                                                                                           v0
                                                                                                                           v1
                                                                                                                           v2
                                                                                                                           v3
                                                                                                                           v4
                                                                                                                           v5
                                                                                                                           v6
                                                                                                                           v16
                                                                                                                           v19)))
                                                                                                                  (coe
                                                                                                                     du28
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v12
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v13
                                                                                                                        v19)
                                                                                                                     (coe
                                                                                                                        d364
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v7
                                                                                                                        v15
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Data.Vec.C22
                                                                                                                           v7
                                                                                                                           v18
                                                                                                                           v19))
                                                                                                                     (coe
                                                                                                                        du368
                                                                                                                        v0
                                                                                                                        v1
                                                                                                                        v2
                                                                                                                        v3
                                                                                                                        v4
                                                                                                                        v5
                                                                                                                        v6
                                                                                                                        v16
                                                                                                                        v19)
                                                                                                                     v18)
                                                                                                                  (coe
                                                                                                                     du242
                                                                                                                     v4
                                                                                                                     (coe
                                                                                                                        du52
                                                                                                                        v4
                                                                                                                        (coe
                                                                                                                           du54
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v12
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              du368
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v13
                                                                                                                              v19))
                                                                                                                        (coe
                                                                                                                           du54
                                                                                                                           v4
                                                                                                                           (coe
                                                                                                                              du52
                                                                                                                              v4
                                                                                                                              (coe
                                                                                                                                 d364
                                                                                                                                 v0
                                                                                                                                 v1
                                                                                                                                 v2
                                                                                                                                 v3
                                                                                                                                 v4
                                                                                                                                 v5
                                                                                                                                 v6
                                                                                                                                 v7
                                                                                                                                 v15
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                                                    v7
                                                                                                                                    v18
                                                                                                                                    v19))
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              du368
                                                                                                                              v0
                                                                                                                              v1
                                                                                                                              v2
                                                                                                                              v3
                                                                                                                              v4
                                                                                                                              v5
                                                                                                                              v6
                                                                                                                              v16
                                                                                                                              v19)))))))))
                                                        _ -> coe MAlonzo.RTE.mazUnreachableError
                                _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1048 = "Algebra.RingSolver.*N-homo"
d1048 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du1048 v0 v1 v2 v3 v4 v5 v6 v8 v9 v10
du1048 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v7 of
        C356 v10 -> case coe v8 of
                        C356 v11 -> coe du200 v5 v10 v11
                        _ -> coe MAlonzo.RTE.mazUnreachableError
        C360 v10 v11 -> case coe v8 of
                            C360 v12 v13 -> coe d1038 v0 v1 v2 v3 v4 v5 v6 v10 v11 v13 v9
                            _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1178 = "Algebra.RingSolver.^N-homo"
d1178 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
        0 -> coe du838 v0 v1 v2 v3 v4 v5 v6 v10
        _ -> let v11
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v9
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                 (coe du244 v4
                    (coe du368 v0 v1 v2 v3 v4 v5 v6
                       (coe du666 v0 v1 v2 v3 v4 v5 v6 v8
                          (coe d742 v0 v1 v2 v3 v4 v5 v6 v7 v8 v11))
                       v10)
                    (coe du52 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
                       (coe du368 v0 v1 v2 v3 v4 v5 v6
                          (coe d742 v0 v1 v2 v3 v4 v5 v6 v7 v8 v11)
                          v10))
                    (coe du52 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
                       (coe du214 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10) v11))
                    (coe du1048 v0 v1 v2 v3 v4 v5 v6 v8
                       (coe d742 v0 v1 v2 v3 v4 v5 v6 v7 v8 v11)
                       v10)
                    (coe du244 v4
                       (coe du52 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
                          (coe du368 v0 v1 v2 v3 v4 v5 v6
                             (coe d742 v0 v1 v2 v3 v4 v5 v6 v7 v8 v11)
                             v10))
                       (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v4
                          (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
                          (coe du214 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10) v11))
                       (coe du52 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
                          (coe du214 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10) v11))
                       (coe MAlonzo.Code.Function.du176
                          (coe du136 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10))
                          (coe du64 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
                             (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
                             (coe du368 v0 v1 v2 v3 v4 v5 v6
                                (coe d742 v0 v1 v2 v3 v4 v5 v6 v7 v8 v11)
                                v10)
                             (coe du214 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10) v11))
                          (coe d1178 v0 v1 v2 v3 v4 v5 v6 v7 v8 v11 v10))
                       (coe du242 v4
                          (coe du52 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10)
                             (coe du214 v4 (coe du368 v0 v1 v2 v3 v4 v5 v6 v8 v10) v11)))))
name1196 = "Algebra.RingSolver.-H\8255-homo"
d1196 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
        MAlonzo.Code.Data.Vec.C22 v10 v11 v12 -> coe
                                                   MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                   (coe du244 v4
                                                      (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                         (coe d654 v0 v1 v2 v3 v4 v5 v6 v7
                                                            (coe du756 v0 v1 v2 v3 v4 v5 v6
                                                               (coe d580 v0 v1 v2 v3 v4 v5 v6 v7))
                                                            v8)
                                                         (coe MAlonzo.Code.Data.Vec.C22 v7 v11 v12))
                                                      (coe du52 v4
                                                         (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                            (coe du756 v0 v1 v2 v3 v4 v5 v6
                                                               (coe d580 v0 v1 v2 v3 v4 v5 v6 v7))
                                                            v12)
                                                         (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                            (coe MAlonzo.Code.Data.Vec.C22 v7 v11
                                                               v12)))
                                                      (coe du98 v4
                                                         (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                            (coe MAlonzo.Code.Data.Vec.C22 v7 v11
                                                               v12)))
                                                      (coe d1016 v0 v1 v2 v3 v4 v5 v6 v7
                                                         (coe du756 v0 v1 v2 v3 v4 v5 v6
                                                            (coe d580 v0 v1 v2 v3 v4 v5 v6 v7))
                                                         v8
                                                         v11
                                                         v12)
                                                      (coe du244 v4
                                                         (coe du52 v4
                                                            (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                               (coe du756 v0 v1 v2 v3 v4 v5 v6
                                                                  (coe d580 v0 v1 v2 v3 v4 v5 v6
                                                                     v7))
                                                               v12)
                                                            (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                               (coe MAlonzo.Code.Data.Vec.C22 v7 v11
                                                                  v12)))
                                                         (coe
                                                            MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                            v4
                                                            (coe
                                                               MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d168
                                                               v4
                                                               (coe du108 v4))
                                                            (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                               (coe MAlonzo.Code.Data.Vec.C22 v7 v11
                                                                  v12)))
                                                         (coe du98 v4
                                                            (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                               (coe MAlonzo.Code.Data.Vec.C22 v7 v11
                                                                  v12)))
                                                         (coe MAlonzo.Code.Function.du176
                                                            (coe du146 v4
                                                               (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                                  (coe du756 v0 v1 v2 v3 v4 v5 v6
                                                                     (coe d580 v0 v1 v2 v3 v4 v5 v6
                                                                        v7))
                                                                  v12)
                                                               (coe du98 v4
                                                                  (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                                     (coe d580 v0 v1 v2 v3 v4 v5 v6
                                                                        v7)
                                                                     v12))
                                                               (coe
                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d168
                                                                  v4
                                                                  (coe du108 v4))
                                                               (coe du1204 v0 v1 v2 v3 v4 v5 v6
                                                                  (coe d580 v0 v1 v2 v3 v4 v5 v6 v7)
                                                                  v12)
                                                               (coe du104 v4
                                                                  (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                                     (coe d580 v0 v1 v2 v3 v4 v5 v6
                                                                        v7)
                                                                     v12)
                                                                  (coe du108 v4)
                                                                  (coe du838 v0 v1 v2 v3 v4 v5 v6
                                                                     v12)))
                                                            (coe du64 v4
                                                               (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                                  (coe du756 v0 v1 v2 v3 v4 v5 v6
                                                                     (coe d580 v0 v1 v2 v3 v4 v5 v6
                                                                        v7))
                                                                  v12)
                                                               (coe
                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d168
                                                                  v4
                                                                  (coe du108 v4))
                                                               (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                                  (coe MAlonzo.Code.Data.Vec.C22 v7
                                                                     v11
                                                                     v12))
                                                               (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                                  (coe MAlonzo.Code.Data.Vec.C22 v7
                                                                     v11
                                                                     v12)))
                                                            (coe du136 v4
                                                               (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                                  (coe MAlonzo.Code.Data.Vec.C22 v7
                                                                     v11
                                                                     v12))))
                                                         (coe du244 v4
                                                            (coe du52 v4
                                                               (coe du98 v4 (coe du108 v4))
                                                               (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                                  (coe MAlonzo.Code.Data.Vec.C22 v7
                                                                     v11
                                                                     v12)))
                                                            (coe
                                                               MAlonzo.Code.Algebra.RingSolver.Lemmas.du80
                                                               v4
                                                               (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                                  (coe MAlonzo.Code.Data.Vec.C22 v7
                                                                     v11
                                                                     v12)))
                                                            (coe du98 v4
                                                               (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                                  (coe MAlonzo.Code.Data.Vec.C22 v7
                                                                     v11
                                                                     v12)))
                                                            (coe du34 v4
                                                               (coe d364 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                                                  (coe MAlonzo.Code.Data.Vec.C22 v7
                                                                     v11
                                                                     v12)))
                                                            (coe du242 v4
                                                               (coe du98 v4
                                                                  (coe d364 v0 v1 v2 v3 v4 v5 v6 v7
                                                                     v8
                                                                     (coe MAlonzo.Code.Data.Vec.C22
                                                                        v7
                                                                        v11
                                                                        v12)))))))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1204 = "Algebra.RingSolver.-N\8255-homo"
d1204 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du1204 v0 v1 v2 v3 v4 v5 v6 v8 v9
du1204 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
        C356 v9 -> coe du204 v5 v9
        C360 v9 v10 -> coe d1196 v0 v1 v2 v3 v4 v5 v6 v9 v10 v8
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1224 = "Algebra.RingSolver.correct-con"
d1224 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du1224 v0 v1 v2 v3 v4 v5 v6 v8 v9
du1224 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
        MAlonzo.Code.Data.Vec.C14 -> coe du136 v4
                                       (coe du368 v0 v1 v2 v3 v4 v5 v6
                                          (coe d766 v0 v1 v2 v3 v4 v5 v6 (0 :: Integer) v7)
                                          (coe MAlonzo.Code.Data.Vec.C14))
        MAlonzo.Code.Data.Vec.C22 v9 v10 v11 -> coe
                                                  MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                  (coe du244 v4
                                                     (coe d364 v0 v1 v2 v3 v4 v5 v6 v9
                                                        (coe d588 v0 v1 v2 v3 v4 v5 v6 v9
                                                           (coe C350 v9)
                                                           (coe d766 v0 v1 v2 v3 v4 v5 v6 v9 v7))
                                                        (coe MAlonzo.Code.Data.Vec.C22 v9 v10 v11))
                                                     (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                        (coe d766 v0 v1 v2 v3 v4 v5 v6 v9 v7)
                                                        v11)
                                                     (coe du210 v5 v7)
                                                     (coe d896 v0 v1 v2 v3 v4 v5 v6 v9
                                                        (coe d766 v0 v1 v2 v3 v4 v5 v6 v9 v7)
                                                        v10
                                                        v11)
                                                     (coe du244 v4
                                                        (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                           (coe d766 v0 v1 v2 v3 v4 v5 v6 v9 v7)
                                                           v11)
                                                        (coe du210 v5 v7)
                                                        (coe du210 v5 v7)
                                                        (coe du1224 v0 v1 v2 v3 v4 v5 v6 v7 v11)
                                                        (coe du242 v4 (coe du210 v5 v7))))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1240 = "Algebra.RingSolver.correct-var"
d1240 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du1240 v0 v1 v2 v3 v4 v5 v6 v8 v9
du1240 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
        MAlonzo.Code.Data.Vec.C22 v9 v10 v11 -> case coe v7 of
                                                    MAlonzo.Code.Data.Fin.C8 v12 -> coe
                                                                                      MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                                                      (coe du244 v4
                                                                                         (coe du54
                                                                                            v4
                                                                                            (coe
                                                                                               du52
                                                                                               v4
                                                                                               (coe
                                                                                                  du54
                                                                                                  v4
                                                                                                  (coe
                                                                                                     du52
                                                                                                     v4
                                                                                                     (coe
                                                                                                        du106
                                                                                                        v4)
                                                                                                     v10)
                                                                                                  (coe
                                                                                                     du368
                                                                                                     v0
                                                                                                     v1
                                                                                                     v2
                                                                                                     v3
                                                                                                     v4
                                                                                                     v5
                                                                                                     v6
                                                                                                     (coe
                                                                                                        d580
                                                                                                        v0
                                                                                                        v1
                                                                                                        v2
                                                                                                        v3
                                                                                                        v4
                                                                                                        v5
                                                                                                        v6
                                                                                                        v12)
                                                                                                     v11))
                                                                                               v10)
                                                                                            (coe
                                                                                               du368
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               (coe
                                                                                                  du570
                                                                                                  v3
                                                                                                  v12)
                                                                                               v11))
                                                                                         (coe
                                                                                            MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                            v4
                                                                                            (coe
                                                                                               MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                               v4
                                                                                               (coe
                                                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                  v4
                                                                                                  (coe
                                                                                                     du52
                                                                                                     v4
                                                                                                     (coe
                                                                                                        du106
                                                                                                        v4)
                                                                                                     v10)
                                                                                                  (coe
                                                                                                     du108
                                                                                                     v4))
                                                                                               v10)
                                                                                            (coe
                                                                                               du106
                                                                                               v4))
                                                                                         v10
                                                                                         (coe
                                                                                            MAlonzo.Code.Function.du176
                                                                                            (coe
                                                                                               MAlonzo.Code.Function.du176
                                                                                               (coe
                                                                                                  MAlonzo.Code.Function.du176
                                                                                                  (coe
                                                                                                     du136
                                                                                                     v4
                                                                                                     (coe
                                                                                                        du52
                                                                                                        v4
                                                                                                        (coe
                                                                                                           du106
                                                                                                           v4)
                                                                                                        v10))
                                                                                                  (coe
                                                                                                     du84
                                                                                                     v4
                                                                                                     (coe
                                                                                                        du52
                                                                                                        v4
                                                                                                        (coe
                                                                                                           du106
                                                                                                           v4)
                                                                                                        v10)
                                                                                                     (coe
                                                                                                        du52
                                                                                                        v4
                                                                                                        (coe
                                                                                                           du106
                                                                                                           v4)
                                                                                                        v10)
                                                                                                     (coe
                                                                                                        du368
                                                                                                        v0
                                                                                                        v1
                                                                                                        v2
                                                                                                        v3
                                                                                                        v4
                                                                                                        v5
                                                                                                        v6
                                                                                                        (coe
                                                                                                           d580
                                                                                                           v0
                                                                                                           v1
                                                                                                           v2
                                                                                                           v3
                                                                                                           v4
                                                                                                           v5
                                                                                                           v6
                                                                                                           v12)
                                                                                                        v11)
                                                                                                     (coe
                                                                                                        du108
                                                                                                        v4))
                                                                                                  (coe
                                                                                                     du838
                                                                                                     v0
                                                                                                     v1
                                                                                                     v2
                                                                                                     v3
                                                                                                     v4
                                                                                                     v5
                                                                                                     v6
                                                                                                     v11))
                                                                                               (coe
                                                                                                  du64
                                                                                                  v4
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                     v4
                                                                                                     (coe
                                                                                                        du52
                                                                                                        v4
                                                                                                        (coe
                                                                                                           du106
                                                                                                           v4)
                                                                                                        v10)
                                                                                                     (coe
                                                                                                        du368
                                                                                                        v0
                                                                                                        v1
                                                                                                        v2
                                                                                                        v3
                                                                                                        v4
                                                                                                        v5
                                                                                                        v6
                                                                                                        (coe
                                                                                                           d580
                                                                                                           v0
                                                                                                           v1
                                                                                                           v2
                                                                                                           v3
                                                                                                           v4
                                                                                                           v5
                                                                                                           v6
                                                                                                           v12)
                                                                                                        v11))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                     v4
                                                                                                     (coe
                                                                                                        du52
                                                                                                        v4
                                                                                                        (coe
                                                                                                           du106
                                                                                                           v4)
                                                                                                        v10)
                                                                                                     (coe
                                                                                                        du108
                                                                                                        v4))
                                                                                                  v10
                                                                                                  v10)
                                                                                               (coe
                                                                                                  du136
                                                                                                  v4
                                                                                                  v10))
                                                                                            (coe
                                                                                               du84
                                                                                               v4
                                                                                               (coe
                                                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                  v4
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                     v4
                                                                                                     (coe
                                                                                                        du52
                                                                                                        v4
                                                                                                        (coe
                                                                                                           du106
                                                                                                           v4)
                                                                                                        v10)
                                                                                                     (coe
                                                                                                        du368
                                                                                                        v0
                                                                                                        v1
                                                                                                        v2
                                                                                                        v3
                                                                                                        v4
                                                                                                        v5
                                                                                                        v6
                                                                                                        (coe
                                                                                                           d580
                                                                                                           v0
                                                                                                           v1
                                                                                                           v2
                                                                                                           v3
                                                                                                           v4
                                                                                                           v5
                                                                                                           v6
                                                                                                           v12)
                                                                                                        v11))
                                                                                                  v10)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                                                                  v4
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                                                                     v4
                                                                                                     (coe
                                                                                                        du52
                                                                                                        v4
                                                                                                        (coe
                                                                                                           du106
                                                                                                           v4)
                                                                                                        v10)
                                                                                                     (coe
                                                                                                        du108
                                                                                                        v4))
                                                                                                  v10)
                                                                                               (coe
                                                                                                  du368
                                                                                                  v0
                                                                                                  v1
                                                                                                  v2
                                                                                                  v3
                                                                                                  v4
                                                                                                  v5
                                                                                                  v6
                                                                                                  (coe
                                                                                                     du570
                                                                                                     v3
                                                                                                     v12)
                                                                                                  v11)
                                                                                               (coe
                                                                                                  du106
                                                                                                  v4))
                                                                                            (coe
                                                                                               du814
                                                                                               v0
                                                                                               v1
                                                                                               v2
                                                                                               v3
                                                                                               v4
                                                                                               v5
                                                                                               v6
                                                                                               v11))
                                                                                         (coe du244
                                                                                            v4
                                                                                            (coe
                                                                                               du54
                                                                                               v4
                                                                                               (coe
                                                                                                  du52
                                                                                                  v4
                                                                                                  (coe
                                                                                                     du54
                                                                                                     v4
                                                                                                     (coe
                                                                                                        du52
                                                                                                        v4
                                                                                                        (coe
                                                                                                           du106
                                                                                                           v4)
                                                                                                        v10)
                                                                                                     (coe
                                                                                                        du108
                                                                                                        v4))
                                                                                                  v10)
                                                                                               (coe
                                                                                                  du106
                                                                                                  v4))
                                                                                            v10
                                                                                            v10
                                                                                            (coe
                                                                                               du30
                                                                                               v4
                                                                                               v10)
                                                                                            (coe
                                                                                               du242
                                                                                               v4
                                                                                               v10)))
                                                    MAlonzo.Code.Data.Fin.C14 v12 v13 -> coe
                                                                                           MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                                                           (coe
                                                                                              du244
                                                                                              v4
                                                                                              (coe
                                                                                                 d364
                                                                                                 v0
                                                                                                 v1
                                                                                                 v2
                                                                                                 v3
                                                                                                 v4
                                                                                                 v5
                                                                                                 v6
                                                                                                 v12
                                                                                                 (coe
                                                                                                    d588
                                                                                                    v0
                                                                                                    v1
                                                                                                    v2
                                                                                                    v3
                                                                                                    v4
                                                                                                    v5
                                                                                                    v6
                                                                                                    v12
                                                                                                    (coe
                                                                                                       C350
                                                                                                       v12)
                                                                                                    (coe
                                                                                                       du776
                                                                                                       v0
                                                                                                       v1
                                                                                                       v2
                                                                                                       v3
                                                                                                       v4
                                                                                                       v5
                                                                                                       v6
                                                                                                       v13))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.Vec.C22
                                                                                                    v12
                                                                                                    v10
                                                                                                    v11))
                                                                                              (coe
                                                                                                 du368
                                                                                                 v0
                                                                                                 v1
                                                                                                 v2
                                                                                                 v3
                                                                                                 v4
                                                                                                 v5
                                                                                                 v6
                                                                                                 (coe
                                                                                                    du776
                                                                                                    v0
                                                                                                    v1
                                                                                                    v2
                                                                                                    v3
                                                                                                    v4
                                                                                                    v5
                                                                                                    v6
                                                                                                    v13)
                                                                                                 v11)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.Vec.du696
                                                                                                 v13
                                                                                                 v11)
                                                                                              (coe
                                                                                                 d896
                                                                                                 v0
                                                                                                 v1
                                                                                                 v2
                                                                                                 v3
                                                                                                 v4
                                                                                                 v5
                                                                                                 v6
                                                                                                 v12
                                                                                                 (coe
                                                                                                    du776
                                                                                                    v0
                                                                                                    v1
                                                                                                    v2
                                                                                                    v3
                                                                                                    v4
                                                                                                    v5
                                                                                                    v6
                                                                                                    v13)
                                                                                                 v10
                                                                                                 v11)
                                                                                              (coe
                                                                                                 du244
                                                                                                 v4
                                                                                                 (coe
                                                                                                    du368
                                                                                                    v0
                                                                                                    v1
                                                                                                    v2
                                                                                                    v3
                                                                                                    v4
                                                                                                    v5
                                                                                                    v6
                                                                                                    (coe
                                                                                                       du776
                                                                                                       v0
                                                                                                       v1
                                                                                                       v2
                                                                                                       v3
                                                                                                       v4
                                                                                                       v5
                                                                                                       v6
                                                                                                       v13)
                                                                                                    v11)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.Vec.du696
                                                                                                    v13
                                                                                                    v11)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.Vec.du696
                                                                                                    v13
                                                                                                    v11)
                                                                                                 (coe
                                                                                                    du1240
                                                                                                    v0
                                                                                                    v1
                                                                                                    v2
                                                                                                    v3
                                                                                                    v4
                                                                                                    v5
                                                                                                    v6
                                                                                                    v13
                                                                                                    v11)
                                                                                                 (coe
                                                                                                    du242
                                                                                                    v4
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.Vec.du696
                                                                                                       v13
                                                                                                       v11))))
                                                    _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1258 = "Algebra.RingSolver.correct"
d1258 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
        C276 v10 v11 v12 -> case coe v10 of
                                C260 -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                          (coe du244 v4
                                             (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                (coe du616 v0 v1 v2 v3 v4 v5 v6
                                                   (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v11)
                                                   (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v12))
                                                v9)
                                             (coe du54 v4
                                                (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                   (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v11)
                                                   v9)
                                                (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                   (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v12)
                                                   v9))
                                             (coe du54 v4 (coe du316 v4 v5 v11 v9)
                                                (coe du316 v4 v5 v12 v9))
                                             (coe du942 v0 v1 v2 v3 v4 v5 v6
                                                (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v11)
                                                (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v12)
                                                v9)
                                             (coe du244 v4
                                                (coe du54 v4
                                                   (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v11 v9)
                                                   (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v12 v9))
                                                (coe
                                                   MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                                   v4
                                                   (coe du316 v4 v5 v11 v9)
                                                   (coe du316 v4 v5 v12 v9))
                                                (coe du54 v4 (coe du316 v4 v5 v11 v9)
                                                   (coe du316 v4 v5 v12 v9))
                                                (coe MAlonzo.Code.Function.du176
                                                   (coe d1258 v0 v1 v2 v3 v4 v5 v6 v7 v11 v9)
                                                   (coe du84 v4
                                                      (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v11 v9)
                                                      (coe du316 v4 v5 v11 v9)
                                                      (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v12 v9)
                                                      (coe du316 v4 v5 v12 v9))
                                                   (coe d1258 v0 v1 v2 v3 v4 v5 v6 v7 v12 v9))
                                                (coe du242 v4
                                                   (coe du54 v4 (coe du316 v4 v5 v11 v9)
                                                      (coe du316 v4 v5 v12 v9)))))
                                C262 -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                          (coe du244 v4
                                             (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                (coe du666 v0 v1 v2 v3 v4 v5 v6
                                                   (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v11)
                                                   (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v12))
                                                v9)
                                             (coe du52 v4
                                                (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                   (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v11)
                                                   v9)
                                                (coe du368 v0 v1 v2 v3 v4 v5 v6
                                                   (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v12)
                                                   v9))
                                             (coe du52 v4 (coe du316 v4 v5 v11 v9)
                                                (coe du316 v4 v5 v12 v9))
                                             (coe du1048 v0 v1 v2 v3 v4 v5 v6
                                                (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v11)
                                                (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v12)
                                                v9)
                                             (coe du244 v4
                                                (coe du52 v4
                                                   (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v11 v9)
                                                   (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v12 v9))
                                                (coe
                                                   MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                                   v4
                                                   (coe du316 v4 v5 v11 v9)
                                                   (coe du316 v4 v5 v12 v9))
                                                (coe du52 v4 (coe du316 v4 v5 v11 v9)
                                                   (coe du316 v4 v5 v12 v9))
                                                (coe MAlonzo.Code.Function.du176
                                                   (coe d1258 v0 v1 v2 v3 v4 v5 v6 v7 v11 v9)
                                                   (coe du64 v4
                                                      (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v11 v9)
                                                      (coe du316 v4 v5 v11 v9)
                                                      (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v12 v9)
                                                      (coe du316 v4 v5 v12 v9))
                                                   (coe d1258 v0 v1 v2 v3 v4 v5 v6 v7 v12 v9))
                                                (coe du242 v4
                                                   (coe du52 v4 (coe du316 v4 v5 v11 v9)
                                                      (coe du316 v4 v5 v12 v9)))))
                                _ -> coe MAlonzo.RTE.mazUnreachableError
        C280 v10 -> coe du1224 v0 v1 v2 v3 v4 v5 v6 v10 v9
        C284 v10 -> coe du1240 v0 v1 v2 v3 v4 v5 v6 v10 v9
        C290 v10 v11 -> coe
                          MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                          (coe du244 v4
                             (coe du368 v0 v1 v2 v3 v4 v5 v6
                                (coe d742 v0 v1 v2 v3 v4 v5 v6 v7
                                   (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v10)
                                   v11)
                                v9)
                             (coe du214 v4
                                (coe du368 v0 v1 v2 v3 v4 v5 v6
                                   (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v10)
                                   v9)
                                v11)
                             (coe du214 v4 (coe du316 v4 v5 v10 v9) v11)
                             (coe d1178 v0 v1 v2 v3 v4 v5 v6 v7
                                (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v10)
                                v11
                                v9)
                             (coe du244 v4
                                (coe du214 v4 (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v10 v9) v11)
                                (coe MAlonzo.Code.Algebra.Operations.du130 (coe du140 v4)
                                   (coe du316 v4 v5 v10 v9)
                                   v11)
                                (coe du214 v4 (coe du316 v4 v5 v10 v9) v11)
                                (coe MAlonzo.Code.Function.du176
                                   (coe d1258 v0 v1 v2 v3 v4 v5 v6 v7 v10 v9)
                                   (coe du222 v4 (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v10 v9)
                                      (coe du316 v4 v5 v10 v9)
                                      v11
                                      v11)
                                   erased)
                                (coe du242 v4 (coe du214 v4 (coe du316 v4 v5 v10 v9) v11))))
        C294 v10 -> coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                      (coe du244 v4
                         (coe du368 v0 v1 v2 v3 v4 v5 v6
                            (coe du756 v0 v1 v2 v3 v4 v5 v6
                               (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v10))
                            v9)
                         (coe du98 v4
                            (coe du368 v0 v1 v2 v3 v4 v5 v6
                               (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v10)
                               v9))
                         (coe du98 v4 (coe du316 v4 v5 v10 v9))
                         (coe du1204 v0 v1 v2 v3 v4 v5 v6
                            (coe d782 v0 v1 v2 v3 v4 v5 v6 v7 v10)
                            v9)
                         (coe du244 v4
                            (coe du98 v4 (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v10 v9))
                            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d168 v4
                               (coe du316 v4 v5 v10 v9))
                            (coe du98 v4 (coe du316 v4 v5 v10 v9))
                            (coe du104 v4 (coe d804 v0 v1 v2 v3 v4 v5 v6 v7 v10 v9)
                               (coe du316 v4 v5 v10 v9)
                               (coe d1258 v0 v1 v2 v3 v4 v5 v6 v7 v10 v9))
                            (coe du242 v4 (coe du98 v4 (coe du316 v4 v5 v10 v9)))))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1292 = "Algebra.RingSolver._._\8860_"
d1292 v0 v1 v2 v3 v4 v5 v6 = du1292
du1292
  = coe MAlonzo.Code.Relation.Binary.Reflection.d138 erased erased
      erased
      erased
      erased
      erased
      erased
      erased
      erased
      erased
name1294 = "Algebra.RingSolver._.prove"
d1294 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Relation.Binary.Reflection.d86 erased erased
      erased
      erased
      erased
      (coe du142 v4)
      erased
      (coe d316 erased erased erased erased v4 v5 erased)
      (coe d804 v0 v1 v2 v3 v4 v5 v6)
      (coe d1258 v0 v1 v2 v3 v4 v5 v6)
name1296 = "Algebra.RingSolver._.solve"
d1296 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Relation.Binary.Reflection.d110 erased erased
      erased
      erased
      erased
      (coe du142 v4)
      (\ v7 -> coe C284)
      (coe d316 erased erased erased erased v4 v5 erased)
      (coe d804 v0 v1 v2 v3 v4 v5 v6)
      (coe d1258 v0 v1 v2 v3 v4 v5 v6)