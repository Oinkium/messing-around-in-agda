{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Nat.Properties where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified
       MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing
import qualified MAlonzo.Code.Algebra.RingSolver.Simple
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties.Simple
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary
name8 = "Data.Nat.Properties._.refl"
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
name14 = "Data.Nat.Properties._._DistributesOver_"
d14 = erased
name22 = "Data.Nat.Properties._.Absorptive"
d22 = erased
name32 = "Data.Nat.Properties._.Identity"
d32 = erased
name50 = "Data.Nat.Properties._.Zero"
d50 = erased
name56 = "Data.Nat.Properties.isCommutativeSemiring"
d56
  = coe MAlonzo.Code.Algebra.Structures.C313
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.C25
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
            erased
            erased)
         erased
         erased)
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.C25
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
            erased
            erased)
         erased
         erased)
      erased
      erased
name62 = "Data.Nat.Properties.commutativeSemiring"
d62
  = coe MAlonzo.Code.Algebra.C239 erased erased
      ((Prelude.+) :: Integer -> Integer -> Integer)
      ((Prelude.*) :: Integer -> Integer -> Integer)
      (0 :: Integer)
      (1 :: Integer)
      d56
name66 = "Data.Nat.Properties.SemiringSolver._*H_"
d66
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d118 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name68 = "Data.Nat.Properties.SemiringSolver._*HN_"
d68
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d120 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name70 = "Data.Nat.Properties.SemiringSolver._*N_"
d70
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d122 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name72 = "Data.Nat.Properties.SemiringSolver._*NH_"
d72
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d124 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name78 = "Data.Nat.Properties.SemiringSolver._*x+H_"
d78
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d130 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name80 = "Data.Nat.Properties.SemiringSolver._*x+HN_"
d80
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d132 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name82 = "Data.Nat.Properties.SemiringSolver._+H_"
d82
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d134 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name84 = "Data.Nat.Properties.SemiringSolver._+N_"
d84
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d136 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name86 = "Data.Nat.Properties.SemiringSolver._:*_"
d86
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d138 erased erased
      erased
      erased
name88 = "Data.Nat.Properties.SemiringSolver._:+_"
d88
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d140 erased erased
      erased
      erased
name90 = "Data.Nat.Properties.SemiringSolver._:-_"
d90
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d142 erased erased
      erased
      erased
name92 = "Data.Nat.Properties.SemiringSolver._\8860_"
d92 = MAlonzo.Code.Algebra.RingSolver.Simple.du144
name96 = "Data.Nat.Properties.SemiringSolver._^N_"
d96
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d148 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name98 = "Data.Nat.Properties.SemiringSolver._\8776H_"
d98 a0 a1 a2 = ()
name100 = "Data.Nat.Properties.SemiringSolver._\8776N_"
d100 a0 a1 a2 = ()
name102 = "Data.Nat.Properties.SemiringSolver._\8799H_"
d102
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d154 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name104 = "Data.Nat.Properties.SemiringSolver._\8799N_"
d104
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d156 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name106 = "Data.Nat.Properties.SemiringSolver.*H-homo"
d106 = erased
name108 = "Data.Nat.Properties.SemiringSolver.*HN-homo"
d108 = erased
name110 = "Data.Nat.Properties.SemiringSolver.*N-homo"
d110 = erased
name112 = "Data.Nat.Properties.SemiringSolver.*NH-homo"
d112 = erased
name114 = "Data.Nat.Properties.SemiringSolver.*x+H-homo"
d114 = erased
name116 = "Data.Nat.Properties.SemiringSolver.*x+HN\8776*x+"
d116 = erased
name118 = "Data.Nat.Properties.SemiringSolver.+H-homo"
d118 = erased
name120 = "Data.Nat.Properties.SemiringSolver.+N-homo"
d120 = erased
name122 = "Data.Nat.Properties.SemiringSolver.-H_"
d122
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d174 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name124 = "Data.Nat.Properties.SemiringSolver.-H\8255-homo"
d124 = erased
name126 = "Data.Nat.Properties.SemiringSolver.-N_"
d126
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d178 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name128 = "Data.Nat.Properties.SemiringSolver.-N\8255-homo"
d128 = erased
name130 = "Data.Nat.Properties.SemiringSolver.0H"
d130 = MAlonzo.Code.Algebra.RingSolver.Simple.du182
name132 = "Data.Nat.Properties.SemiringSolver.0N"
d132
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.du184
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
name134 = "Data.Nat.Properties.SemiringSolver.0N-homo"
d134 = erased
name136
  = "Data.Nat.Properties.SemiringSolver.0\8776\10214\&0\10215"
d136 = erased
name138 = "Data.Nat.Properties.SemiringSolver.1H"
d138
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d190 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name140 = "Data.Nat.Properties.SemiringSolver.1N"
d140
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d192 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name142 = "Data.Nat.Properties.SemiringSolver.1N-homo"
d142 = erased
name146 = "Data.Nat.Properties.SemiringSolver.HNF"
d146 a0 = ()
name148 = "Data.Nat.Properties.SemiringSolver.Normal"
d148 a0 = ()
name150 = "Data.Nat.Properties.SemiringSolver.Op"
d150 = ()
name152 = "Data.Nat.Properties.SemiringSolver.Polynomial"
d152 a0 = ()
name158 = "Data.Nat.Properties.SemiringSolver.^N-homo"
d158 = erased
name166 = "Data.Nat.Properties.SemiringSolver.correct"
d166 = erased
name168 = "Data.Nat.Properties.SemiringSolver.correct-con"
d168 = erased
name170 = "Data.Nat.Properties.SemiringSolver.correct-var"
d170 = erased
name172 = "Data.Nat.Properties.SemiringSolver.normalise"
d172
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d224 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name174 = "Data.Nat.Properties.SemiringSolver.normalise-con"
d174
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d226 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name176 = "Data.Nat.Properties.SemiringSolver.normalise-var"
d176
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d228 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name184 = "Data.Nat.Properties.SemiringSolver.prove"
d184 = erased
name186 = "Data.Nat.Properties.SemiringSolver.sem"
d186
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.du238
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
name188 = "Data.Nat.Properties.SemiringSolver.solve"
d188
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d240 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name196 = "Data.Nat.Properties.SemiringSolver.\8709*x+HN-homo"
d196 = erased
name198 = "Data.Nat.Properties.SemiringSolver.\10214_\10215"
d198
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.du250
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
name200 = "Data.Nat.Properties.SemiringSolver.\10214_\10215H"
d200
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d252 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name202 = "Data.Nat.Properties.SemiringSolver.\10214_\10215H-cong"
d202 = erased
name204 = "Data.Nat.Properties.SemiringSolver.\10214_\10215N"
d204
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d256 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name206 = "Data.Nat.Properties.SemiringSolver.\10214_\10215N-cong"
d206 = erased
name208 = "Data.Nat.Properties.SemiringSolver.\10214_\10215\8595"
d208
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d260 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d62)
      MAlonzo.Code.Data.Nat.Base.d220
name252 = "Data.Nat.Properties.\8852-assoc"
d252 = erased
name268 = "Data.Nat.Properties.\8852-identity"
d268 = coe MAlonzo.Code.Data.Product.C30 erased erased
name274 = "Data.Nat.Properties._.n\8852\&0\8801n"
d274 = erased
name280 = "Data.Nat.Properties.\8852-comm"
d280 = erased
name290 = "Data.Nat.Properties.\8851-assoc"
d290 = erased
name306 = "Data.Nat.Properties.\8851-zero"
d306 = coe MAlonzo.Code.Data.Product.C30 erased erased
name312 = "Data.Nat.Properties._.n\8851\&0\8801\&0"
d312 = erased
name318 = "Data.Nat.Properties.\8851-comm"
d318 = erased
name328 = "Data.Nat.Properties.distrib-\8851-\8852"
d328 = coe MAlonzo.Code.Data.Product.C30 erased erased
name334 = "Data.Nat.Properties._.distrib\691-\8851-\8852"
d334 = erased
name354 = "Data.Nat.Properties._.distrib\737-\8851-\8852"
d354 = erased
name362
  = "Data.Nat.Properties.\8852-\8851-0-isCommutativeSemiringWithoutOne"
d362
  = coe MAlonzo.Code.Algebra.Structures.C287
      (coe MAlonzo.Code.Algebra.Structures.C199
         (coe MAlonzo.Code.Algebra.Structures.C71
            (coe MAlonzo.Code.Algebra.Structures.C25
               MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
               erased
               erased)
            (coe MAlonzo.Code.Data.Product.d26 d268)
            erased)
         (coe MAlonzo.Code.Algebra.Structures.C25
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
            erased
            erased)
         d328
         d306)
      erased
name364
  = "Data.Nat.Properties.\8852-\8851-0-commutativeSemiringWithoutOne"
d364
  = coe MAlonzo.Code.Algebra.C217 erased erased
      MAlonzo.Code.Data.Nat.Base.d192
      MAlonzo.Code.Data.Nat.Base.d202
      (0 :: Integer)
      d362
name366 = "Data.Nat.Properties.absorptive-\8851-\8852"
d366 = coe MAlonzo.Code.Data.Product.C30 erased erased
name372 = "Data.Nat.Properties._.abs-\8852-\8851"
d372 = erased
name382 = "Data.Nat.Properties._.abs-\8851-\8852"
d382 = erased
name392 = "Data.Nat.Properties.isDistributiveLattice"
d392
  = coe MAlonzo.Code.Algebra.Structures.C573
      (coe MAlonzo.Code.Algebra.Structures.C539
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
         erased
         erased
         erased
         erased
         erased
         erased
         d366)
      (coe MAlonzo.Code.Data.Product.d28 d328)
name394 = "Data.Nat.Properties.distributiveLattice"
d394
  = coe MAlonzo.Code.Algebra.C355 erased erased
      MAlonzo.Code.Data.Nat.Base.d202
      MAlonzo.Code.Data.Nat.Base.d192
      d392
name400 = "Data.Nat.Properties.\8804-step"
d400 v0 v1 v2 = du400 v1 v2
du400 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.Nat.Base.C10 v2 -> coe
                                               MAlonzo.Code.Data.Nat.Base.C10
                                               (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                                                  (1 :: Integer)
                                                  v0)
        MAlonzo.Code.Data.Nat.Base.C18 v2 v3 v4 -> coe
                                                     MAlonzo.Code.Data.Nat.Base.C18
                                                     v2
                                                     (coe
                                                        ((Prelude.+) :: Integer -> Integer -> Integer)
                                                        (1 :: Integer)
                                                        v3)
                                                     (coe du400 v3 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name404 = "Data.Nat.Properties.\8804\8242\8658\8804"
d404 v0 v1 v2 = du404 v0 v2
du404 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.Nat.Base.C68 -> coe d8 v0
        MAlonzo.Code.Data.Nat.Base.C74 v2 v3 -> coe du400 v2
                                                  (coe du404 v0 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name410 = "Data.Nat.Properties.z\8804\8242n"
d410 v0
  = case coe v0 of
        0 -> coe MAlonzo.Code.Data.Nat.Base.C68
        _ -> let v1
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in coe MAlonzo.Code.Data.Nat.Base.C74 v1 (coe d410 v1)
name418 = "Data.Nat.Properties.s\8804\8242s"
d418 v0 v1 v2 = du418 v2
du418 v0
  = case coe v0 of
        MAlonzo.Code.Data.Nat.Base.C68 -> coe
                                            MAlonzo.Code.Data.Nat.Base.C68
        MAlonzo.Code.Data.Nat.Base.C74 v1 v2 -> coe
                                                  MAlonzo.Code.Data.Nat.Base.C74
                                                  (coe
                                                     ((Prelude.+) :: Integer -> Integer -> Integer)
                                                     (1 :: Integer)
                                                     v1)
                                                  (coe du418 v2)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name422 = "Data.Nat.Properties.\8804\8658\8804\8242"
d422 v0 v1 v2 = du422 v1 v2
du422 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.Nat.Base.C10 v2 -> coe d410 v0
        MAlonzo.Code.Data.Nat.Base.C18 v2 v3 v4 -> coe du418
                                                     (coe du422 v3 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name432 = "Data.Nat.Properties.\8804-steps"
d432 v0 v1 v2 v3 = du432 v1 v2 v3
du432 v0 v1 v2
  = case coe v1 of
        0 -> coe v2
        _ -> let v3
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in
               coe du400
                 (coe ((Prelude.+) :: Integer -> Integer -> Integer) v3 v0)
                 (coe du432 v0 v3 v2)
name444 = "Data.Nat.Properties.m\8804m+n"
d444 v0 v1
  = case coe v0 of
        0 -> coe MAlonzo.Code.Data.Nat.Base.C10 v1
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Data.Nat.Base.C18 v2
                 (coe ((Prelude.+) :: Integer -> Integer -> Integer) v2 v1)
                 (coe d444 v2 v1)
name456 = "Data.Nat.Properties.m\8804\8242m+n"
d456 v0 v1
  = coe du422
      (coe ((Prelude.+) :: Integer -> Integer -> Integer) v0 v1)
      (coe d444 v0 v1)
name466 = "Data.Nat.Properties.n\8804\8242m+n"
d466 v0 v1
  = case coe v0 of
        0 -> coe MAlonzo.Code.Data.Nat.Base.C68
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Data.Nat.Base.C74
                 (coe ((Prelude.+) :: Integer -> Integer -> Integer) v2 v1)
                 (coe d466 v2 v1)
name478 = "Data.Nat.Properties.n\8804m+n"
d478 v0 v1 = coe du404 v1 (coe d466 v0 v1)
name486 = "Data.Nat.Properties.n\8804\&1+n"
d486 v0 = coe du400 v0 (coe d8 v0)
name490 = "Data.Nat.Properties.1+n\8816n"
d490 = erased
name498 = "Data.Nat.Properties.\8804pred\8658\8804"
d498 v0 v1 v2 = du498 v1 v2
du498 v0 v1
  = case coe v0 of
        0 -> coe v1
        _ -> coe du400 (coe MAlonzo.Code.Data.Nat.Base.d180 v0) v1
name514 = "Data.Nat.Properties.\8804\8658pred\8804"
d514 v0 v1 v2
  = case coe v0 of
        0 -> coe v2
        _ -> let v3
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                 (coe MAlonzo.Code.Data.Nat.d76 v3 v0 v1 (coe d486 v3)
                    (coe MAlonzo.Code.Data.Nat.d76 v0 v1 v1 v2
                       (coe MAlonzo.Code.Data.Nat.d70 v1)))
name530 = "Data.Nat.Properties.<\8658\8804pred"
d530 v0 v1 v2 = du530 v2
du530 v0
  = case coe v0 of
        MAlonzo.Code.Data.Nat.Base.C18 v1 v2 v3 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name538 = "Data.Nat.Properties.\172i+1+j\8804i"
d538 = erased
name548 = "Data.Nat.Properties.n\8760m\8804n"
d548 v0 v1
  = case coe v0 of
        0 -> coe d8
               (coe MAlonzo.Code.Agda.Builtin.Nat.d22 v1 (0 :: Integer))
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   0 -> coe d8
                          (coe MAlonzo.Code.Agda.Builtin.Nat.d22 (0 :: Integer) v0)
                   _ -> let v3
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                  (1 :: Integer)
                          in
                          coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                            (coe MAlonzo.Code.Data.Nat.d76
                               (coe MAlonzo.Code.Agda.Builtin.Nat.d22 v3 v2)
                               v3
                               v1
                               (coe d548 v2 v3)
                               (coe MAlonzo.Code.Data.Nat.d76 v3 v1 v1 (coe d486 v3)
                                  (coe MAlonzo.Code.Data.Nat.d70 v1)))
name562 = "Data.Nat.Properties.n\8804m+n\8760m"
d562 v0 v1
  = case coe v1 of
        0 -> coe MAlonzo.Code.Data.Nat.Base.C10
               (coe ((Prelude.+) :: Integer -> Integer -> Integer)
                  (coe MAlonzo.Code.Agda.Builtin.Nat.d22 (0 :: Integer) v0)
                  v0)
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in
               case coe v0 of
                   0 -> coe d8 v1
                   _ -> let v3
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                                  (1 :: Integer)
                          in
                          coe MAlonzo.Code.Data.Nat.Base.C18 v2
                            (coe ((Prelude.+) :: Integer -> Integer -> Integer) v3
                               (coe MAlonzo.Code.Agda.Builtin.Nat.d22 v2 v3))
                            (coe d562 v3 v2)
name576 = "Data.Nat.Properties.m\8851n\8804m"
d576 v0 v1
  = case coe v0 of
        0 -> coe MAlonzo.Code.Data.Nat.Base.C10 (0 :: Integer)
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   0 -> coe MAlonzo.Code.Data.Nat.Base.C10 v0
                   _ -> let v3
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                  (1 :: Integer)
                          in
                          coe MAlonzo.Code.Function.du158
                            (coe MAlonzo.Code.Data.Nat.Base.C18
                               (coe MAlonzo.Code.Data.Nat.Base.d202 v2 v3)
                               v2)
                            (coe d576 v2 v3)
name588 = "Data.Nat.Properties.m\8804m\8852n"
d588 v0 v1
  = case coe v0 of
        0 -> coe MAlonzo.Code.Data.Nat.Base.C10
               (coe MAlonzo.Code.Data.Nat.Base.d192 (0 :: Integer) v1)
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   0 -> coe d8 v0
                   _ -> let v3
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                  (1 :: Integer)
                          in
                          coe MAlonzo.Code.Function.du158
                            (coe MAlonzo.Code.Data.Nat.Base.C18 v2
                               (coe MAlonzo.Code.Data.Nat.Base.d192 v2 v3))
                            (coe d588 v2 v3)
name598 = "Data.Nat.Properties.\8968n/2\8969\8804\8242n"
d598 v0
  = case coe v0 of
        0 -> coe MAlonzo.Code.Data.Nat.Base.C68
        1 -> coe MAlonzo.Code.Data.Nat.Base.C68
        _ -> let v1
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (2 :: Integer)
               in coe du418 (coe MAlonzo.Code.Data.Nat.Base.C74 v1 (coe d598 v1))
name604 = "Data.Nat.Properties.\8970n/2\8971\8804\8242n"
d604 v0
  = case coe v0 of
        0 -> coe MAlonzo.Code.Data.Nat.Base.C68
        _ -> let v1
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in coe MAlonzo.Code.Data.Nat.Base.C74 v1 (coe d598 v1)
name608 = "Data.Nat.Properties.<-trans"
d608 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe MAlonzo.Code.Data.Nat.d76
         (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
            v0)
         v1
         v2
         v3
         (coe MAlonzo.Code.Data.Nat.d76 v1
            (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
               v1)
            v2
            (coe d486 v1)
            (coe MAlonzo.Code.Data.Nat.d76
               (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                  v1)
               v2
               v2
               v4
               (coe MAlonzo.Code.Data.Nat.d70 v2))))
name620 = "Data.Nat.Properties.\8816\8658>"
d620 v0 v1 v2 = du620 v0 v1
du620 v0 v1
  = case coe v0 of
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   0 -> coe MAlonzo.Code.Data.Nat.Base.C18 (0 :: Integer) v2
                          (coe MAlonzo.Code.Data.Nat.Base.C10 v2)
                   _ -> let v3
                              = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                                  (1 :: Integer)
                          in coe MAlonzo.Code.Data.Nat.Base.C18 v1 v2 (coe du620 v2 v3)
name638 = "Data.Nat.Properties.\8804\8243\8658\8804"
d638 v0 v1 v2 = du638 v0 v2
du638 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.Nat.Base.C112 v2 v3 -> coe d444 v0 v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name640 = "Data.Nat.Properties.\8804\8658\8804\8243"
d640 v0 v1 v2 = du640 v0 v1
du640 v0 v1
  = coe MAlonzo.Code.Data.Nat.Base.C112 (coe du652 v0 v1) erased
name652 = "Data.Nat.Properties._.k"
d652 v0 v1 v2 v3 v4 v5 = du652 v3 v4
du652 v0 v1
  = case coe v0 of
        0 -> coe v1
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               let v3
                     = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                         (1 :: Integer)
                 in coe du652 v2 v3
name670 = "Data.Nat.Properties._.proof"
d670 = erased
name678 = "Data.Nat.Properties.m\8802\&1+m+n"
d678 = erased
name684 = "Data.Nat.Properties.strictTotalOrder"
d684
  = coe MAlonzo.Code.Relation.Binary.C683 erased erased erased
      (coe MAlonzo.Code.Relation.Binary.C561
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
         d608
         d698)
name694 = "Data.Nat.Properties._.2+m+n\8816m"
d694 = erased
name698 = "Data.Nat.Properties._.cmp"
d698 v0 v1
  = let v2 = coe MAlonzo.Code.Data.Nat.Base.d300 v0 v1 in
      case coe v2 of
          MAlonzo.Code.Data.Nat.Base.C284 v3 v4 -> coe
                                                     MAlonzo.Code.Relation.Binary.Core.C400
                                                     (coe d444
                                                        (coe
                                                           ((Prelude.+) :: Integer -> Integer -> Integer)
                                                           (1 :: Integer)
                                                           v3)
                                                        v4)
                                                     erased
                                                     erased
          MAlonzo.Code.Data.Nat.Base.C288 v3 -> coe
                                                  MAlonzo.Code.Relation.Binary.Core.C408
                                                  erased
                                                  erased
                                                  erased
          MAlonzo.Code.Data.Nat.Base.C294 v3 v4 -> coe
                                                     MAlonzo.Code.Relation.Binary.Core.C416
                                                     erased
                                                     (coe MAlonzo.Code.Function.d38 erased erased
                                                        erased
                                                        erased
                                                        erased
                                                        erased
                                                        erased
                                                        erased)
                                                     (coe d444
                                                        (coe
                                                           ((Prelude.+) :: Integer -> Integer -> Integer)
                                                           (1 :: Integer)
                                                           v3)
                                                        v4)
          _ -> coe MAlonzo.RTE.mazUnreachableError
name718 = "Data.Nat.Properties.0\8760n\8801\&0"
d718 = erased
name722 = "Data.Nat.Properties.n\8760n\8801\&0"
d722 = erased
name732 = "Data.Nat.Properties.\8760-+-assoc"
d732 = erased
name760 = "Data.Nat.Properties.+-\8760-assoc"
d760 = erased
name780 = "Data.Nat.Properties.m+n\8760n\8801m"
d780 = erased
name790 = "Data.Nat.Properties.m+n\8760m\8801n"
d790 = erased
name804 = "Data.Nat.Properties.m\8851n+n\8760m\8801n"
d804 = erased
name818 = "Data.Nat.Properties.[m\8760n]\8851[n\8760m]\8801\&0"
d818 = erased
name834 = "Data.Nat.Properties.[i+j]\8760[i+k]\8801j\8760k"
d834 = erased
name852 = "Data.Nat.Properties.i\8760k\8760j+j\8760k\8801i+j\8760k"
d852 = erased
name884 = "Data.Nat.Properties.i+j\8801\&0\8658i\8801\&0"
d884 = erased
name894 = "Data.Nat.Properties.i+j\8801\&0\8658j\8801\&0"
d894 = erased
name906
  = "Data.Nat.Properties.i*j\8801\&0\8658i\8801\&0\8744j\8801\&0"
d906 v0 v1 v2 = du906 v0
du906 v0
  = case coe v0 of
        0 -> coe Left erased
        _ -> coe Right erased
name924 = "Data.Nat.Properties.i*j\8801\&1\8658i\8801\&1"
d924 = erased
name952 = "Data.Nat.Properties.i*j\8801\&1\8658j\8801\&1"
d952 = erased
name966 = "Data.Nat.Properties.cancel-+-left"
d966 = erased
name980 = "Data.Nat.Properties.cancel-+-left-\8804"
d980 v0 v1 v2 v3 = du980 v0 v3
du980 v0 v1
  = case coe v0 of
        0 -> coe v1
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               case coe v1 of
                   MAlonzo.Code.Data.Nat.Base.C18 v3 v4 v5 -> coe du980 v2 v5
                   _ -> coe MAlonzo.RTE.mazUnreachableError
name994 = "Data.Nat.Properties.cancel-*-right"
d994 = erased
name1016 = "Data.Nat.Properties.cancel-*-right-\8804"
d1016 v0 v1 v2 v3 = du1016 v0 v1
du1016 v0 v1
  = case coe v0 of
        0 -> coe MAlonzo.Code.Data.Nat.Base.C10 v1
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               let v3
                     = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                         (1 :: Integer)
                 in coe MAlonzo.Code.Data.Nat.Base.C18 v2 v3 (coe du1016 v2 v3)
name1028 = "Data.Nat.Properties.*-distrib-\8760\691"
d1028 = erased
name1052 = "Data.Nat.Properties.im\8801jm+n\8658[i\8760j]m\8801n"
d1052 = erased
name1068 = "Data.Nat.Properties.i+1+j\8802i"
d1068 = erased
name1108 = "Data.Nat.Properties._._.reflexive"
d1108 v0 v1 v2 = du1108
du1108
  = coe MAlonzo.Code.Relation.Binary.d38
      (coe MAlonzo.Code.Relation.Binary.d268
         (coe MAlonzo.Code.Relation.Binary.d842
            (coe MAlonzo.Code.Relation.Binary.d970
               (coe MAlonzo.Code.Relation.Binary.d1052
                  MAlonzo.Code.Data.Nat.d12))))
name1144 = "Data.Nat.Properties.\8970n/2\8971-mono"
d1144 v0 v1 v2 = du1144 v1 v2
du1144 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.Nat.Base.C10 v2 -> coe
                                               MAlonzo.Code.Data.Nat.Base.C10
                                               (coe MAlonzo.Code.Data.Nat.Base.d212 v0)
        MAlonzo.Code.Data.Nat.Base.C18 v2 v3 v4 -> case coe v4 of
                                                       MAlonzo.Code.Data.Nat.Base.C10 v5 -> coe
                                                                                              MAlonzo.Code.Data.Nat.Base.C10
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.Nat.Base.d212
                                                                                                 (coe
                                                                                                    ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                                                    (1 ::
                                                                                                       Integer)
                                                                                                    v3))
                                                       MAlonzo.Code.Data.Nat.Base.C18 v5 v6
                                                         v7 -> coe MAlonzo.Code.Data.Nat.Base.C18
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Base.d212
                                                                    v5)
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Base.d212
                                                                    v6)
                                                                 (coe du1144 v6 v7)
                                                       _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1148 = "Data.Nat.Properties.\8968n/2\8969-mono"
d1148 v0 v1 v2
  = coe du1144
      (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
         v1)
      (coe MAlonzo.Code.Data.Nat.Base.C18 v0 v1 v2)
name1152 = "Data.Nat.Properties.pred-mono"
d1152 v0 v1 v2 = du1152 v1 v2
du1152 v0 v1
  = case coe v1 of
        MAlonzo.Code.Data.Nat.Base.C10 v2 -> coe
                                               MAlonzo.Code.Data.Nat.Base.C10
                                               (coe MAlonzo.Code.Data.Nat.Base.d180 v0)
        MAlonzo.Code.Data.Nat.Base.C18 v2 v3 v4 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1156 = "Data.Nat.Properties._+-mono_"
d1156 v0 v1 v2 v3 v4 v5
  = let v6
          = case coe v4 of
                MAlonzo.Code.Data.Nat.Base.C18 v6 v7 v8 -> coe
                                                             MAlonzo.Code.Data.Nat.Base.C18
                                                             (coe
                                                                ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                v2
                                                                v6)
                                                             (coe
                                                                ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                v3
                                                                v7)
                                                             (coe d1156 v6 v7 v2 v3 v8 v5)
                _ -> coe MAlonzo.RTE.mazUnreachableError
      in
      case coe v0 of
          0 -> case coe v4 of
                   MAlonzo.Code.Data.Nat.Base.C10 v7 -> coe
                                                          MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                          (coe MAlonzo.Code.Data.Nat.d76 v2 v3
                                                             (coe
                                                                ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                v1
                                                                v3)
                                                             v5
                                                             (coe MAlonzo.Code.Data.Nat.d76 v3
                                                                (coe
                                                                   ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                   v1
                                                                   v3)
                                                                (coe
                                                                   ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                   v1
                                                                   v3)
                                                                (coe d478 v1 v3)
                                                                (coe MAlonzo.Code.Data.Nat.d70
                                                                   (coe
                                                                      ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                      v1
                                                                      v3))))
                   _ -> coe v6
          _ -> coe v6
name1170 = "Data.Nat.Properties._*-mono_"
d1170 v0 v1 v2 v3 v4 v5 = du1170 v1 v2 v3 v4 v5
du1170 v0 v1 v2 v3 v4
  = case coe v3 of
        MAlonzo.Code.Data.Nat.Base.C10 v5 -> coe
                                               MAlonzo.Code.Data.Nat.Base.C10
                                               (coe ((Prelude.*) :: Integer -> Integer -> Integer)
                                                  v0
                                                  v2)
        MAlonzo.Code.Data.Nat.Base.C18 v5 v6 v7 -> coe d1156 v1 v2
                                                     (coe
                                                        ((Prelude.*) :: Integer -> Integer -> Integer)
                                                        v5
                                                        v1)
                                                     (coe
                                                        ((Prelude.*) :: Integer -> Integer -> Integer)
                                                        v6
                                                        v2)
                                                     v4
                                                     (coe du1170 v6 v1 v2 v7 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1178 = "Data.Nat.Properties.\8760-mono"
d1178 v0 v1 v2 v3 v4 v5 = du1178 v0 v1 v4 v5
du1178 v0 v1 v2 v3
  = let v4
          = case coe v3 of
                MAlonzo.Code.Data.Nat.Base.C10 v4 -> coe
                                                       MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
                                                       (coe MAlonzo.Code.Data.Nat.d76
                                                          (coe MAlonzo.Code.Agda.Builtin.Nat.d22 v0
                                                             v4)
                                                          v0
                                                          v1
                                                          (coe d548 v4 v0)
                                                          (coe MAlonzo.Code.Data.Nat.d76 v0 v1 v1 v2
                                                             (coe MAlonzo.Code.Data.Nat.d70 v1)))
                _ -> coe MAlonzo.RTE.mazUnreachableError
      in
      case coe v2 of
          MAlonzo.Code.Data.Nat.Base.C10 v5 -> case coe v3 of
                                                   MAlonzo.Code.Data.Nat.Base.C18 v6 v7 v8 -> coe
                                                                                                MAlonzo.Code.Data.Nat.Base.C10
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Nat.d22
                                                                                                   v1
                                                                                                   (coe
                                                                                                      ((Prelude.+) :: Integer -> Integer -> Integer)
                                                                                                      (1 ::
                                                                                                         Integer)
                                                                                                      v6))
                                                   _ -> coe v4
          MAlonzo.Code.Data.Nat.Base.C18 v5 v6 v7 -> case coe v3 of
                                                         MAlonzo.Code.Data.Nat.Base.C18 v8 v9
                                                           v10 -> coe du1178 v5 v6 v7 v10
                                                         _ -> coe v4
          _ -> coe v4