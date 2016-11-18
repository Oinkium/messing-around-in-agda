{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.Structures where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
name14 = "Algebra.Structures.IsSemigroup"
d14 a0 a1 a2 a3 a4 = ()

data T14 a0 a1 a2 = C25 a0 a1 a2
name40 = "Algebra.Structures._.Associative"
d40 = erased
name124 = "Algebra.Structures.IsSemigroup.isEquivalence"
d124 v0
  = case coe v0 of
        C25 v1 v2 v3 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name126 = "Algebra.Structures.IsSemigroup.assoc"
d126 v0
  = case coe v0 of
        C25 v1 v2 v3 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name128 = "Algebra.Structures.IsSemigroup.\8729-cong"
d128 v0
  = case coe v0 of
        C25 v1 v2 v3 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name132 = "Algebra.Structures.IsSemigroup._.refl"
d132 v0 = coe MAlonzo.Code.Relation.Binary.Core.d516 (coe d124 v0)
name134 = "Algebra.Structures.IsSemigroup._.reflexive"
d134 v0 v1 v2 v3 v4 v5 = du134 v5
du134 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d522 erased erased erased
      erased
      (coe d124 v0)
name136 = "Algebra.Structures.IsSemigroup._.sym"
d136 v0 = coe MAlonzo.Code.Relation.Binary.Core.d518 (coe d124 v0)
name138 = "Algebra.Structures.IsSemigroup._.trans"
d138 v0 = coe MAlonzo.Code.Relation.Binary.Core.d520 (coe d124 v0)
name152 = "Algebra.Structures.IsMonoid"
d152 a0 a1 a2 a3 a4 a5 = ()

data T152 a0 a1 = C49 a0 a1
name188 = "Algebra.Structures._.Identity"
d188 = erased
name262 = "Algebra.Structures.IsMonoid.isSemigroup"
d262 v0
  = case coe v0 of
        C49 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name264 = "Algebra.Structures.IsMonoid.identity"
d264 v0
  = case coe v0 of
        C49 v1 v2 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name268 = "Algebra.Structures.IsMonoid._.assoc"
d268 v0 = coe d126 (coe d262 v0)
name270 = "Algebra.Structures.IsMonoid._.isEquivalence"
d270 v0 = coe d124 (coe d262 v0)
name272 = "Algebra.Structures.IsMonoid._.refl"
d272 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124 (coe d262 v0))
name274 = "Algebra.Structures.IsMonoid._.reflexive"
d274 v0 v1 v2 v3 v4 v5 v6 = du274 v6
du274 v0 = coe du134 (coe d262 v0)
name276 = "Algebra.Structures.IsMonoid._.sym"
d276 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124 (coe d262 v0))
name278 = "Algebra.Structures.IsMonoid._.trans"
d278 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124 (coe d262 v0))
name280 = "Algebra.Structures.IsMonoid._.\8729-cong"
d280 v0 = coe d128 (coe d262 v0)
name294 = "Algebra.Structures.IsCommutativeMonoid"
d294 a0 a1 a2 a3 a4 a5 = ()

data T294 a0 a1 a2 = C71 a0 a1 a2
name324 = "Algebra.Structures._.Commutative"
d324 = erased
name336 = "Algebra.Structures._.LeftIdentity"
d336 = erased
name382 = "Algebra.Structures.IsCommutativeMonoid._.Identity"
d382 = erased
name394 = "Algebra.Structures.IsCommutativeMonoid._.RightIdentity"
d394 = erased
name406 = "Algebra.Structures.IsCommutativeMonoid.isSemigroup"
d406 v0
  = case coe v0 of
        C71 v1 v2 v3 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name408 = "Algebra.Structures.IsCommutativeMonoid.identity\737"
d408 v0
  = case coe v0 of
        C71 v1 v2 v3 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name410 = "Algebra.Structures.IsCommutativeMonoid.comm"
d410 v0
  = case coe v0 of
        C71 v1 v2 v3 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name414 = "Algebra.Structures.IsCommutativeMonoid._.assoc"
d414 v0 = coe d126 (coe d406 v0)
name416 = "Algebra.Structures.IsCommutativeMonoid._.isEquivalence"
d416 v0 = coe d124 (coe d406 v0)
name418 = "Algebra.Structures.IsCommutativeMonoid._.refl"
d418 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124 (coe d406 v0))
name420 = "Algebra.Structures.IsCommutativeMonoid._.reflexive"
d420 v0 v1 v2 v3 v4 v5 v6 = du420 v6
du420 v0 = coe du134 (coe d406 v0)
name422 = "Algebra.Structures.IsCommutativeMonoid._.sym"
d422 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124 (coe d406 v0))
name424 = "Algebra.Structures.IsCommutativeMonoid._.trans"
d424 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124 (coe d406 v0))
name426 = "Algebra.Structures.IsCommutativeMonoid._.\8729-cong"
d426 v0 = coe d128 (coe d406 v0)
name428 = "Algebra.Structures.IsCommutativeMonoid.identity"
d428 v0 v1 v2 v3 v4 v5 v6 = du428 v2 v3 v4 v5 v6
du428 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Data.Product.C30 (coe d408 v4)
      (coe d454 erased erased v0 v1 v2 v3 v4)
name438 = "Algebra.Structures.IsCommutativeMonoid._._._\8718"
d438 v0 v1 v2 v3 v4 v5 v6 = du438 v2 v3 v6
du438 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe MAlonzo.Code.Relation.Binary.C85 v0 v1
         (coe d124 (coe d406 v2)))
name440
  = "Algebra.Structures.IsCommutativeMonoid._._._\8764\10216_\10217_"
d440 v0 v1 v2 v3 v4 v5 v6 = du440 v2 v3 v6
du440 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40
      (coe MAlonzo.Code.Relation.Binary.C85 v0 v1
         (coe d124 (coe d406 v2)))
name454 = "Algebra.Structures.IsCommutativeMonoid._.identity\691"
d454 v0 v1 v2 v3 v4 v5 v6 v7 = du454 v2 v3 v4 v5 v6 v7
du454 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du440 v0 v1 v4 (coe v2 v5 v3) (coe v2 v3 v5) v5
         (coe d410 v4 v5 v3)
         (coe du440 v0 v1 v4 (coe v2 v3 v5) v5 v5 (coe d408 v4 v5)
            (coe du438 v0 v1 v4 v5)))
name458 = "Algebra.Structures.IsCommutativeMonoid.isMonoid"
d458 v0 v1 v2 v3 v4 v5 v6 = du458 v2 v3 v4 v5 v6
du458 v0 v1 v2 v3 v4
  = coe C49 (coe d406 v4) (coe du428 v0 v1 v2 v3 v4)
name474 = "Algebra.Structures.IsGroup"
d474 a0 a1 a2 a3 a4 a5 a6 = ()

data T474 a0 a1 a2 = C109 a0 a1 a2
name514 = "Algebra.Structures._.Inverse"
d514 = erased
name588 = "Algebra.Structures.IsGroup.isMonoid"
d588 v0
  = case coe v0 of
        C109 v1 v2 v3 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name590 = "Algebra.Structures.IsGroup.inverse"
d590 v0
  = case coe v0 of
        C109 v1 v2 v3 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name592 = "Algebra.Structures.IsGroup.\8315\185-cong"
d592 v0
  = case coe v0 of
        C109 v1 v2 v3 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name596 = "Algebra.Structures.IsGroup._.assoc"
d596 v0 = coe d126 (coe d262 (coe d588 v0))
name598 = "Algebra.Structures.IsGroup._.identity"
d598 v0 = coe d264 (coe d588 v0)
name600 = "Algebra.Structures.IsGroup._.isEquivalence"
d600 v0 = coe d124 (coe d262 (coe d588 v0))
name602 = "Algebra.Structures.IsGroup._.isSemigroup"
d602 v0 = coe d262 (coe d588 v0)
name604 = "Algebra.Structures.IsGroup._.refl"
d604 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124 (coe d262 (coe d588 v0)))
name606 = "Algebra.Structures.IsGroup._.reflexive"
d606 v0 v1 v2 v3 v4 v5 v6 v7 = du606 v7
du606 v0 = coe du274 (coe d588 v0)
name608 = "Algebra.Structures.IsGroup._.sym"
d608 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124 (coe d262 (coe d588 v0)))
name610 = "Algebra.Structures.IsGroup._.trans"
d610 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124 (coe d262 (coe d588 v0)))
name612 = "Algebra.Structures.IsGroup._.\8729-cong"
d612 v0 = coe d128 (coe d262 (coe d588 v0))
name614 = "Algebra.Structures.IsGroup._-_"
d614 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du614 v4 v6 v8 v9
du614 v0 v1 v2 v3 = coe v0 v2 (coe v1 v3)
name634 = "Algebra.Structures.IsAbelianGroup"
d634 a0 a1 a2 a3 a4 a5 a6 = ()

data T634 a0 a1 = C137 a0 a1
name666 = "Algebra.Structures._.Commutative"
d666 = erased
name746 = "Algebra.Structures.IsAbelianGroup.isGroup"
d746 v0
  = case coe v0 of
        C137 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name748 = "Algebra.Structures.IsAbelianGroup.comm"
d748 v0
  = case coe v0 of
        C137 v1 v2 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name752 = "Algebra.Structures.IsAbelianGroup._._-_"
d752 v0 v1 v2 v3 v4 v5 v6 v7 = du752 v4 v6
du752 v0 v1
  = coe d614 erased erased erased erased v0 erased v1 erased
name754 = "Algebra.Structures.IsAbelianGroup._.assoc"
d754 v0 = coe d126 (coe d262 (coe d588 (coe d746 v0)))
name756 = "Algebra.Structures.IsAbelianGroup._.identity"
d756 v0 = coe d264 (coe d588 (coe d746 v0))
name758 = "Algebra.Structures.IsAbelianGroup._.inverse"
d758 v0 = coe d590 (coe d746 v0)
name760 = "Algebra.Structures.IsAbelianGroup._.isEquivalence"
d760 v0 = coe d124 (coe d262 (coe d588 (coe d746 v0)))
name762 = "Algebra.Structures.IsAbelianGroup._.isMonoid"
d762 v0 = coe d588 (coe d746 v0)
name764 = "Algebra.Structures.IsAbelianGroup._.isSemigroup"
d764 v0 = coe d262 (coe d588 (coe d746 v0))
name766 = "Algebra.Structures.IsAbelianGroup._.refl"
d766 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124 (coe d262 (coe d588 (coe d746 v0))))
name768 = "Algebra.Structures.IsAbelianGroup._.reflexive"
d768 v0 v1 v2 v3 v4 v5 v6 v7 = du768 v7
du768 v0 = coe du606 (coe d746 v0)
name770 = "Algebra.Structures.IsAbelianGroup._.sym"
d770 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124 (coe d262 (coe d588 (coe d746 v0))))
name772 = "Algebra.Structures.IsAbelianGroup._.trans"
d772 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124 (coe d262 (coe d588 (coe d746 v0))))
name774 = "Algebra.Structures.IsAbelianGroup._.\8315\185-cong"
d774 v0 = coe d592 (coe d746 v0)
name776 = "Algebra.Structures.IsAbelianGroup._.\8729-cong"
d776 v0 = coe d128 (coe d262 (coe d588 (coe d746 v0)))
name778 = "Algebra.Structures.IsAbelianGroup.isCommutativeMonoid"
d778 v0
  = coe C71 (coe d262 (coe d588 (coe d746 v0)))
      (coe MAlonzo.Code.Data.Product.d26
         (coe d264 (coe d588 (coe d746 v0))))
      (coe d748 v0)
name794 = "Algebra.Structures.IsNearSemiring"
d794 a0 a1 a2 a3 a4 a5 a6 = ()

data T794 a0 a1 a2 a3 = C169 a0 a1 a2 a3
name816 = "Algebra.Structures._._DistributesOver\691_"
d816 = erased
name842 = "Algebra.Structures._.LeftZero"
d842 = erased
name910 = "Algebra.Structures.IsNearSemiring.+-isMonoid"
d910 v0
  = case coe v0 of
        C169 v1 v2 v3 v4 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name912 = "Algebra.Structures.IsNearSemiring.*-isSemigroup"
d912 v0
  = case coe v0 of
        C169 v1 v2 v3 v4 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name914 = "Algebra.Structures.IsNearSemiring.distrib\691"
d914 v0
  = case coe v0 of
        C169 v1 v2 v3 v4 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name916 = "Algebra.Structures.IsNearSemiring.zero\737"
d916 v0
  = case coe v0 of
        C169 v1 v2 v3 v4 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name920 = "Algebra.Structures.IsNearSemiring._.assoc"
d920 v0 = coe d126 (coe d262 (coe d910 v0))
name922 = "Algebra.Structures.IsNearSemiring._.\8729-cong"
d922 v0 = coe d128 (coe d262 (coe d910 v0))
name924 = "Algebra.Structures.IsNearSemiring._.identity"
d924 v0 = coe d264 (coe d910 v0)
name926 = "Algebra.Structures.IsNearSemiring._.isSemigroup"
d926 v0 = coe d262 (coe d910 v0)
name928 = "Algebra.Structures.IsNearSemiring._.isEquivalence"
d928 v0 = coe d124 (coe d262 (coe d910 v0))
name930 = "Algebra.Structures.IsNearSemiring._.refl"
d930 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124 (coe d262 (coe d910 v0)))
name932 = "Algebra.Structures.IsNearSemiring._.reflexive"
d932 v0 v1 v2 v3 v4 v5 v6 v7 = du932 v7
du932 v0 = coe du274 (coe d910 v0)
name934 = "Algebra.Structures.IsNearSemiring._.sym"
d934 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124 (coe d262 (coe d910 v0)))
name936 = "Algebra.Structures.IsNearSemiring._.trans"
d936 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124 (coe d262 (coe d910 v0)))
name940 = "Algebra.Structures.IsNearSemiring._.assoc"
d940 v0 = coe d126 (coe d912 v0)
name942 = "Algebra.Structures.IsNearSemiring._.\8729-cong"
d942 v0 = coe d128 (coe d912 v0)
name958 = "Algebra.Structures.IsSemiringWithoutOne"
d958 a0 a1 a2 a3 a4 a5 a6 = ()

data T958 a0 a1 a2 a3 = C199 a0 a1 a2 a3
name978 = "Algebra.Structures._._DistributesOver_"
d978 = erased
name1014 = "Algebra.Structures._.Zero"
d1014 = erased
name1074
  = "Algebra.Structures.IsSemiringWithoutOne.+-isCommutativeMonoid"
d1074 v0
  = case coe v0 of
        C199 v1 v2 v3 v4 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1076 = "Algebra.Structures.IsSemiringWithoutOne.*-isSemigroup"
d1076 v0
  = case coe v0 of
        C199 v1 v2 v3 v4 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1078 = "Algebra.Structures.IsSemiringWithoutOne.distrib"
d1078 v0
  = case coe v0 of
        C199 v1 v2 v3 v4 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1080 = "Algebra.Structures.IsSemiringWithoutOne.zero"
d1080 v0
  = case coe v0 of
        C199 v1 v2 v3 v4 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1084 = "Algebra.Structures.IsSemiringWithoutOne._.assoc"
d1084 v0 = coe d126 (coe d406 (coe d1074 v0))
name1086 = "Algebra.Structures.IsSemiringWithoutOne._.comm"
d1086 v0 = coe d410 (coe d1074 v0)
name1088 = "Algebra.Structures.IsSemiringWithoutOne._.\8729-cong"
d1088 v0 = coe d128 (coe d406 (coe d1074 v0))
name1090 = "Algebra.Structures.IsSemiringWithoutOne._.identity"
d1090 v0 v1 v2 v3 v4 v5 v6 v7 = du1090 v2 v3 v4 v6 v7
du1090 v0 v1 v2 v3 v4 = coe du428 v0 v1 v2 v3 (coe d1074 v4)
name1092 = "Algebra.Structures.IsSemiringWithoutOne._.isMonoid"
d1092 v0 v1 v2 v3 v4 v5 v6 v7 = du1092 v2 v3 v4 v6 v7
du1092 v0 v1 v2 v3 v4 = coe du458 v0 v1 v2 v3 (coe d1074 v4)
name1094 = "Algebra.Structures.IsSemiringWithoutOne._.isSemigroup"
d1094 v0 = coe d406 (coe d1074 v0)
name1096
  = "Algebra.Structures.IsSemiringWithoutOne._.isEquivalence"
d1096 v0 = coe d124 (coe d406 (coe d1074 v0))
name1098 = "Algebra.Structures.IsSemiringWithoutOne._.refl"
d1098 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124 (coe d406 (coe d1074 v0)))
name1100 = "Algebra.Structures.IsSemiringWithoutOne._.reflexive"
d1100 v0 v1 v2 v3 v4 v5 v6 v7 = du1100 v7
du1100 v0 = coe du420 (coe d1074 v0)
name1102 = "Algebra.Structures.IsSemiringWithoutOne._.sym"
d1102 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124 (coe d406 (coe d1074 v0)))
name1104 = "Algebra.Structures.IsSemiringWithoutOne._.trans"
d1104 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124 (coe d406 (coe d1074 v0)))
name1108 = "Algebra.Structures.IsSemiringWithoutOne._.assoc"
d1108 v0 = coe d126 (coe d1076 v0)
name1110 = "Algebra.Structures.IsSemiringWithoutOne._.\8729-cong"
d1110 v0 = coe d128 (coe d1076 v0)
name1112 = "Algebra.Structures.IsSemiringWithoutOne.isNearSemiring"
d1112 v0 v1 v2 v3 v4 v5 v6 v7 = du1112 v2 v3 v4 v6 v7
du1112 v0 v1 v2 v3 v4
  = coe C169 (coe du1092 v0 v1 v2 v3 v4) (coe d1076 v4)
      (coe MAlonzo.Code.Data.Product.d28 (coe d1078 v4))
      (coe MAlonzo.Code.Data.Product.d26 (coe d1080 v4))
name1130 = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero"
d1130 a0 a1 a2 a3 a4 a5 a6 a7 = ()

data T1130 a0 a1 a2 = C237 a0 a1 a2
name1152 = "Algebra.Structures._._DistributesOver_"
d1152 = erased
name1246
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid"
d1246 v0
  = case coe v0 of
        C237 v1 v2 v3 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1248
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-isMonoid"
d1248 v0
  = case coe v0 of
        C237 v1 v2 v3 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1250
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero.distrib"
d1250 v0
  = case coe v0 of
        C237 v1 v2 v3 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1254
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.assoc"
d1254 v0 = coe d126 (coe d406 (coe d1246 v0))
name1256
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.comm"
d1256 v0 = coe d410 (coe d1246 v0)
name1258
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.\8729-cong"
d1258 v0 = coe d128 (coe d406 (coe d1246 v0))
name1260
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identity"
d1260 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1260 v2 v3 v4 v6 v8
du1260 v0 v1 v2 v3 v4 = coe du428 v0 v1 v2 v3 (coe d1246 v4)
name1262
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isMonoid"
d1262 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1262 v2 v3 v4 v6 v8
du1262 v0 v1 v2 v3 v4 = coe du458 v0 v1 v2 v3 (coe d1246 v4)
name1264
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isSemigroup"
d1264 v0 = coe d406 (coe d1246 v0)
name1266
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isEquivalence"
d1266 v0 = coe d124 (coe d406 (coe d1246 v0))
name1268
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.refl"
d1268 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124 (coe d406 (coe d1246 v0)))
name1270
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.reflexive"
d1270 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1270 v8
du1270 v0 = coe du420 (coe d1246 v0)
name1272
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.sym"
d1272 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124 (coe d406 (coe d1246 v0)))
name1274
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.trans"
d1274 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124 (coe d406 (coe d1246 v0)))
name1278
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.assoc"
d1278 v0 = coe d126 (coe d262 (coe d1248 v0))
name1280
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.\8729-cong"
d1280 v0 = coe d128 (coe d262 (coe d1248 v0))
name1282
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identity"
d1282 v0 = coe d264 (coe d1248 v0)
name1284
  = "Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isSemigroup"
d1284 v0 = coe d262 (coe d1248 v0)
name1302 = "Algebra.Structures.IsSemiring"
d1302 a0 a1 a2 a3 a4 a5 a6 a7 = ()

data T1302 a0 a1 = C261 a0 a1
name1360 = "Algebra.Structures._.Zero"
d1360 = erased
name1416
  = "Algebra.Structures.IsSemiring.isSemiringWithoutAnnihilatingZero"
d1416 v0
  = case coe v0 of
        C261 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1418 = "Algebra.Structures.IsSemiring.zero"
d1418 v0
  = case coe v0 of
        C261 v1 v2 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1422 = "Algebra.Structures.IsSemiring._.assoc"
d1422 v0 = coe d126 (coe d262 (coe d1248 (coe d1416 v0)))
name1424 = "Algebra.Structures.IsSemiring._.\8729-cong"
d1424 v0 = coe d128 (coe d262 (coe d1248 (coe d1416 v0)))
name1426 = "Algebra.Structures.IsSemiring._.identity"
d1426 v0 = coe d264 (coe d1248 (coe d1416 v0))
name1428 = "Algebra.Structures.IsSemiring._.*-isMonoid"
d1428 v0 = coe d1248 (coe d1416 v0)
name1430 = "Algebra.Structures.IsSemiring._.isSemigroup"
d1430 v0 = coe d262 (coe d1248 (coe d1416 v0))
name1432 = "Algebra.Structures.IsSemiring._.assoc"
d1432 v0 = coe d126 (coe d406 (coe d1246 (coe d1416 v0)))
name1434 = "Algebra.Structures.IsSemiring._.comm"
d1434 v0 = coe d410 (coe d1246 (coe d1416 v0))
name1436 = "Algebra.Structures.IsSemiring._.\8729-cong"
d1436 v0 = coe d128 (coe d406 (coe d1246 (coe d1416 v0)))
name1438 = "Algebra.Structures.IsSemiring._.identity"
d1438 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1438 v2 v3 v4 v6 v8
du1438 v0 v1 v2 v3 v4 = coe du1260 v0 v1 v2 v3 (coe d1416 v4)
name1440 = "Algebra.Structures.IsSemiring._.+-isCommutativeMonoid"
d1440 v0 = coe d1246 (coe d1416 v0)
name1442 = "Algebra.Structures.IsSemiring._.isMonoid"
d1442 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1442 v2 v3 v4 v6 v8
du1442 v0 v1 v2 v3 v4 = coe du1262 v0 v1 v2 v3 (coe d1416 v4)
name1444 = "Algebra.Structures.IsSemiring._.isSemigroup"
d1444 v0 = coe d406 (coe d1246 (coe d1416 v0))
name1446 = "Algebra.Structures.IsSemiring._.distrib"
d1446 v0 = coe d1250 (coe d1416 v0)
name1448 = "Algebra.Structures.IsSemiring._.isEquivalence"
d1448 v0 = coe d124 (coe d406 (coe d1246 (coe d1416 v0)))
name1450 = "Algebra.Structures.IsSemiring._.refl"
d1450 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124 (coe d406 (coe d1246 (coe d1416 v0))))
name1452 = "Algebra.Structures.IsSemiring._.reflexive"
d1452 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1452 v8
du1452 v0 = coe du1270 (coe d1416 v0)
name1454 = "Algebra.Structures.IsSemiring._.sym"
d1454 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124 (coe d406 (coe d1246 (coe d1416 v0))))
name1456 = "Algebra.Structures.IsSemiring._.trans"
d1456 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124 (coe d406 (coe d1246 (coe d1416 v0))))
name1458 = "Algebra.Structures.IsSemiring.isSemiringWithoutOne"
d1458 v0
  = coe C199 (coe d1246 (coe d1416 v0))
      (coe d262 (coe d1248 (coe d1416 v0)))
      (coe d1250 (coe d1416 v0))
      (coe d1418 v0)
name1462 = "Algebra.Structures.IsSemiring._.isNearSemiring"
d1462 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1462 v2 v3 v4 v6 v8
du1462 v0 v1 v2 v3 v4
  = coe du1112 v0 v1 v2 v3
      (coe C199 (coe d1246 (coe d1416 v4))
         (coe d262 (coe d1248 (coe d1416 v4)))
         (coe d1250 (coe d1416 v4))
         (coe d1418 v4))
name1478 = "Algebra.Structures.IsCommutativeSemiringWithoutOne"
d1478 a0 a1 a2 a3 a4 a5 a6 = ()

data T1478 a0 a1 = C287 a0 a1
name1510 = "Algebra.Structures._.Commutative"
d1510 = erased
name1590
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne.isSemiringWithoutOne"
d1590 v0
  = case coe v0 of
        C287 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1592
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne.*-comm"
d1592 v0
  = case coe v0 of
        C287 v1 v2 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1596
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.assoc"
d1596 v0 = coe d126 (coe d1076 (coe d1590 v0))
name1598
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.\8729-cong"
d1598 v0 = coe d128 (coe d1076 (coe d1590 v0))
name1600
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.*-isSemigroup"
d1600 v0 = coe d1076 (coe d1590 v0)
name1602
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.assoc"
d1602 v0 = coe d126 (coe d406 (coe d1074 (coe d1590 v0)))
name1604
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.comm"
d1604 v0 = coe d410 (coe d1074 (coe d1590 v0))
name1606
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.\8729-cong"
d1606 v0 = coe d128 (coe d406 (coe d1074 (coe d1590 v0)))
name1608
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.identity"
d1608 v0 v1 v2 v3 v4 v5 v6 v7 = du1608 v2 v3 v4 v6 v7
du1608 v0 v1 v2 v3 v4 = coe du1090 v0 v1 v2 v3 (coe d1590 v4)
name1610
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.+-isCommutativeMonoid"
d1610 v0 = coe d1074 (coe d1590 v0)
name1612
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.isMonoid"
d1612 v0 v1 v2 v3 v4 v5 v6 v7 = du1612 v2 v3 v4 v6 v7
du1612 v0 v1 v2 v3 v4 = coe du1092 v0 v1 v2 v3 (coe d1590 v4)
name1614
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.isSemigroup"
d1614 v0 = coe d406 (coe d1074 (coe d1590 v0))
name1616
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.distrib"
d1616 v0 = coe d1078 (coe d1590 v0)
name1618
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.isEquivalence"
d1618 v0 = coe d124 (coe d406 (coe d1074 (coe d1590 v0)))
name1620
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.isNearSemiring"
d1620 v0 v1 v2 v3 v4 v5 v6 v7 = du1620 v2 v3 v4 v6 v7
du1620 v0 v1 v2 v3 v4 = coe du1112 v0 v1 v2 v3 (coe d1590 v4)
name1622
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.refl"
d1622 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124 (coe d406 (coe d1074 (coe d1590 v0))))
name1624
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.reflexive"
d1624 v0 v1 v2 v3 v4 v5 v6 v7 = du1624 v7
du1624 v0 = coe du1100 (coe d1590 v0)
name1626
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.sym"
d1626 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124 (coe d406 (coe d1074 (coe d1590 v0))))
name1628
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.trans"
d1628 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124 (coe d406 (coe d1074 (coe d1590 v0))))
name1630
  = "Algebra.Structures.IsCommutativeSemiringWithoutOne._.zero"
d1630 v0 = coe d1080 (coe d1590 v0)
name1648 = "Algebra.Structures.IsCommutativeSemiring"
d1648 a0 a1 a2 a3 a4 a5 a6 a7 = ()

data T1648 a0 a1 a2 a3 = C313 a0 a1 a2 a3
name1672 = "Algebra.Structures._._DistributesOver\691_"
d1672 = erased
name1698 = "Algebra.Structures._.LeftZero"
d1698 = erased
name1724
  = "Algebra.Structures.IsCommutativeSemiring._._DistributesOver_"
d1724 = erased
name1760 = "Algebra.Structures.IsCommutativeSemiring._.Zero"
d1760 = erased
name1766
  = "Algebra.Structures.IsCommutativeSemiring.+-isCommutativeMonoid"
d1766 v0
  = case coe v0 of
        C313 v1 v2 v3 v4 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1768
  = "Algebra.Structures.IsCommutativeSemiring.*-isCommutativeMonoid"
d1768 v0
  = case coe v0 of
        C313 v1 v2 v3 v4 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1770 = "Algebra.Structures.IsCommutativeSemiring.distrib\691"
d1770 v0
  = case coe v0 of
        C313 v1 v2 v3 v4 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1772 = "Algebra.Structures.IsCommutativeSemiring.zero\737"
d1772 v0
  = case coe v0 of
        C313 v1 v2 v3 v4 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1784
  = "Algebra.Structures.IsCommutativeSemiring.+-CM.isEquivalence"
d1784 v0 = coe d124 (coe d406 (coe d1766 v0))
name1798
  = "Algebra.Structures.IsCommutativeSemiring.+-CM.\8729-cong"
d1798 v0 = coe d128 (coe d406 (coe d1766 v0))
name1804 = "Algebra.Structures.IsCommutativeSemiring.*-CM.comm"
d1804 v0 = coe d410 (coe d1768 v0)
name1812 = "Algebra.Structures.IsCommutativeSemiring.*-CM.isMonoid"
d1812 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1812 v2 v3 v5 v7 v8
du1812 v0 v1 v2 v3 v4 = coe du458 v0 v1 v2 v3 (coe d1768 v4)
name1830 = "Algebra.Structures.IsCommutativeSemiring._._\8718"
d1830 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1830 v2 v3 v8
du1830 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe MAlonzo.Code.Relation.Binary.C85 v0 v1
         (coe d124 (coe d406 (coe d1766 v2))))
name1832
  = "Algebra.Structures.IsCommutativeSemiring._._\8764\10216_\10217_"
d1832 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1832 v2 v3 v8
du1832 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40
      (coe MAlonzo.Code.Relation.Binary.C85 v0 v1
         (coe d124 (coe d406 (coe d1766 v2))))
name1846 = "Algebra.Structures.IsCommutativeSemiring.distrib"
d1846 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1846 v2 v3 v4 v5 v8
du1846 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Data.Product.C30
      (coe d1852 erased erased v0 v1 v2 v3 erased erased v4)
      (coe d1770 v4)
name1852 = "Algebra.Structures.IsCommutativeSemiring._.distrib\737"
d1852 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du1852 v2 v3 v4 v5 v8 v9 v10 v11
du1852 v0 v1 v2 v3 v4 v5 v6 v7
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du1832 v0 v1 v4 (coe v3 v5 (coe v2 v6 v7))
         (coe v3 (coe v2 v6 v7) v5)
         (coe v2 (coe v3 v5 v6) (coe v3 v5 v7))
         (coe d410 (coe d1768 v4) v5 (coe v2 v6 v7))
         (coe du1832 v0 v1 v4 (coe v3 (coe v2 v6 v7) v5)
            (coe v2 (coe v3 v6 v5) (coe v3 v7 v5))
            (coe v2 (coe v3 v5 v6) (coe v3 v5 v7))
            (coe d1770 v4 v5 v6 v7)
            (coe du1832 v0 v1 v4 (coe v2 (coe v3 v6 v5) (coe v3 v7 v5))
               (coe v2 (coe v3 v5 v6) (coe v3 v5 v7))
               (coe v2 (coe v3 v5 v6) (coe v3 v5 v7))
               (coe MAlonzo.Code.Function.du176 (coe d410 (coe d1768 v4) v6 v5)
                  (coe d128 (coe d406 (coe d1766 v4)) (coe v3 v6 v5) (coe v3 v5 v6)
                     (coe v3 v7 v5)
                     (coe v3 v5 v7))
                  (coe d410 (coe d1768 v4) v7 v5))
               (coe du1830 v0 v1 v4 (coe v2 (coe v3 v5 v6) (coe v3 v5 v7))))))
name1860 = "Algebra.Structures.IsCommutativeSemiring.zero"
d1860 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1860 v2 v3 v5 v6 v8
du1860 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Data.Product.C30 (coe d1772 v4)
      (coe d1866 erased erased v0 v1 erased v2 v3 erased v4)
name1866 = "Algebra.Structures.IsCommutativeSemiring._.zero\691"
d1866 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du1866 v2 v3 v5 v6 v8 v9
du1866 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du1832 v0 v1 v4 (coe v2 v5 v3) (coe v2 v3 v5) v3
         (coe d410 (coe d1768 v4) v5 v3)
         (coe du1832 v0 v1 v4 (coe v2 v3 v5) v3 v3 (coe d1772 v4 v5)
            (coe du1830 v0 v1 v4 v3)))
name1870 = "Algebra.Structures.IsCommutativeSemiring.isSemiring"
d1870 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1870 v2 v3 v4 v5 v6 v7 v8
du1870 v0 v1 v2 v3 v4 v5 v6
  = coe C261
      (coe C237 (coe d1766 v6) (coe du1812 v0 v1 v3 v5 v6)
         (coe du1846 v0 v1 v2 v3 v6))
      (coe du1860 v0 v1 v3 v4 v6)
name1874 = "Algebra.Structures.IsCommutativeSemiring._.assoc"
d1874 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1874 v2 v3 v4 v5 v6 v7 v8
du1874 v0 v1 v2 v3 v4 v5 v6
  = coe d126
      (coe d262
         (coe d1248 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6))))
name1876 = "Algebra.Structures.IsCommutativeSemiring._.\8729-cong"
d1876 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1876 v2 v3 v4 v5 v6 v7 v8
du1876 v0 v1 v2 v3 v4 v5 v6
  = coe d128
      (coe d262
         (coe d1248 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6))))
name1878 = "Algebra.Structures.IsCommutativeSemiring._.identity"
d1878 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1878 v2 v3 v4 v5 v6 v7 v8
du1878 v0 v1 v2 v3 v4 v5 v6
  = coe d264
      (coe d1248 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6)))
name1880 = "Algebra.Structures.IsCommutativeSemiring._.*-isMonoid"
d1880 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1880 v2 v3 v4 v5 v6 v7 v8
du1880 v0 v1 v2 v3 v4 v5 v6
  = coe d1248 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6))
name1882 = "Algebra.Structures.IsCommutativeSemiring._.isSemigroup"
d1882 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1882 v2 v3 v4 v5 v6 v7 v8
du1882 v0 v1 v2 v3 v4 v5 v6
  = coe d262
      (coe d1248 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6)))
name1884 = "Algebra.Structures.IsCommutativeSemiring._.assoc"
d1884 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1884 v2 v3 v4 v5 v6 v7 v8
du1884 v0 v1 v2 v3 v4 v5 v6
  = coe d126
      (coe d406
         (coe d1246 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6))))
name1886 = "Algebra.Structures.IsCommutativeSemiring._.comm"
d1886 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1886 v2 v3 v4 v5 v6 v7 v8
du1886 v0 v1 v2 v3 v4 v5 v6
  = coe d410
      (coe d1246 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6)))
name1888 = "Algebra.Structures.IsCommutativeSemiring._.\8729-cong"
d1888 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1888 v2 v3 v4 v5 v6 v7 v8
du1888 v0 v1 v2 v3 v4 v5 v6
  = coe d128
      (coe d406
         (coe d1246 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6))))
name1890 = "Algebra.Structures.IsCommutativeSemiring._.identity"
d1890 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1890 v2 v3 v4 v5 v6 v7 v8
du1890 v0 v1 v2 v3 v4 v5 v6
  = coe du1438 v0 v1 v2 v4 (coe du1870 v0 v1 v2 v3 v4 v5 v6)
name1892 = "Algebra.Structures.IsCommutativeSemiring._.isMonoid"
d1892 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1892 v2 v3 v4 v5 v6 v7 v8
du1892 v0 v1 v2 v3 v4 v5 v6
  = coe du1442 v0 v1 v2 v4 (coe du1870 v0 v1 v2 v3 v4 v5 v6)
name1894 = "Algebra.Structures.IsCommutativeSemiring._.isSemigroup"
d1894 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1894 v2 v3 v4 v5 v6 v7 v8
du1894 v0 v1 v2 v3 v4 v5 v6
  = coe d406
      (coe d1246 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6)))
name1896
  = "Algebra.Structures.IsCommutativeSemiring._.isEquivalence"
d1896 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1896 v2 v3 v4 v5 v6 v7 v8
du1896 v0 v1 v2 v3 v4 v5 v6
  = coe d124
      (coe d406
         (coe d1246 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6))))
name1898
  = "Algebra.Structures.IsCommutativeSemiring._.isNearSemiring"
d1898 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1898 v2 v3 v4 v5 v6 v7 v8
du1898 v0 v1 v2 v3 v4 v5 v6
  = coe du1462 v0 v1 v2 v4 (coe du1870 v0 v1 v2 v3 v4 v5 v6)
name1900
  = "Algebra.Structures.IsCommutativeSemiring._.isSemiringWithoutAnnihilatingZero"
d1900 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1900 v2 v3 v4 v5 v6 v7 v8
du1900 v0 v1 v2 v3 v4 v5 v6
  = coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6)
name1902
  = "Algebra.Structures.IsCommutativeSemiring._.isSemiringWithoutOne"
d1902 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1902 v2 v3 v4 v5 v6 v7 v8
du1902 v0 v1 v2 v3 v4 v5 v6
  = coe C199
      (coe d1246 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6)))
      (coe d262
         (coe d1248 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6))))
      (coe d1250 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6)))
      (coe d1418 (coe du1870 v0 v1 v2 v3 v4 v5 v6))
name1904 = "Algebra.Structures.IsCommutativeSemiring._.refl"
d1904 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1904 v2 v3 v4 v5 v6 v7 v8
du1904 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124
         (coe d406
            (coe d1246 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6)))))
name1906 = "Algebra.Structures.IsCommutativeSemiring._.reflexive"
d1906 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1906 v2 v3 v4 v5 v6 v7 v8
du1906 v0 v1 v2 v3 v4 v5 v6
  = coe du1452 (coe du1870 v0 v1 v2 v3 v4 v5 v6)
name1908 = "Algebra.Structures.IsCommutativeSemiring._.sym"
d1908 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1908 v2 v3 v4 v5 v6 v7 v8
du1908 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124
         (coe d406
            (coe d1246 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6)))))
name1910 = "Algebra.Structures.IsCommutativeSemiring._.trans"
d1910 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1910 v2 v3 v4 v5 v6 v7 v8
du1910 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124
         (coe d406
            (coe d1246 (coe d1416 (coe du1870 v0 v1 v2 v3 v4 v5 v6)))))
name1912
  = "Algebra.Structures.IsCommutativeSemiring.isCommutativeSemiringWithoutOne"
d1912 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du1912 v2 v3 v4 v5 v6 v7 v8
du1912 v0 v1 v2 v3 v4 v5 v6
  = coe C287 (coe du1902 v0 v1 v2 v3 v4 v5 v6)
      (coe d410 (coe d1768 v6))
name1932 = "Algebra.Structures.IsRing"
d1932 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()

data T1932 a0 a1 a2 = C363 a0 a1 a2
name1956 = "Algebra.Structures._._DistributesOver_"
d1956 = erased
name2044 = "Algebra.Structures.IsRing._.Zero"
d2044 = erased
name2050 = "Algebra.Structures.IsRing.+-isAbelianGroup"
d2050 v0
  = case coe v0 of
        C363 v1 v2 v3 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2052 = "Algebra.Structures.IsRing.*-isMonoid"
d2052 v0
  = case coe v0 of
        C363 v1 v2 v3 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2054 = "Algebra.Structures.IsRing.distrib"
d2054 v0
  = case coe v0 of
        C363 v1 v2 v3 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2058 = "Algebra.Structures.IsRing._._-_"
d2058 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2058 v4 v6
du2058 v0 v1 = coe du752 v0 v1
name2060 = "Algebra.Structures.IsRing._.assoc"
d2060 v0 = coe d126 (coe d262 (coe d588 (coe d746 (coe d2050 v0))))
name2062 = "Algebra.Structures.IsRing._.comm"
d2062 v0 = coe d748 (coe d2050 v0)
name2064 = "Algebra.Structures.IsRing._.\8729-cong"
d2064 v0 = coe d128 (coe d262 (coe d588 (coe d746 (coe d2050 v0))))
name2066 = "Algebra.Structures.IsRing._.identity"
d2066 v0 = coe d264 (coe d588 (coe d746 (coe d2050 v0)))
name2068 = "Algebra.Structures.IsRing._.isCommutativeMonoid"
d2068 v0
  = coe C71 (coe d262 (coe d588 (coe d746 (coe d2050 v0))))
      (coe MAlonzo.Code.Data.Product.d26
         (coe d264 (coe d588 (coe d746 (coe d2050 v0)))))
      (coe d748 (coe d2050 v0))
name2070 = "Algebra.Structures.IsRing._.isGroup"
d2070 v0 = coe d746 (coe d2050 v0)
name2072 = "Algebra.Structures.IsRing._.isMonoid"
d2072 v0 = coe d588 (coe d746 (coe d2050 v0))
name2074 = "Algebra.Structures.IsRing._.isSemigroup"
d2074 v0 = coe d262 (coe d588 (coe d746 (coe d2050 v0)))
name2076 = "Algebra.Structures.IsRing._.\8315\185-cong"
d2076 v0 = coe d592 (coe d746 (coe d2050 v0))
name2078 = "Algebra.Structures.IsRing._.inverse"
d2078 v0 = coe d590 (coe d746 (coe d2050 v0))
name2080 = "Algebra.Structures.IsRing._.isEquivalence"
d2080 v0 = coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v0))))
name2082 = "Algebra.Structures.IsRing._.refl"
d2082 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v0)))))
name2084 = "Algebra.Structures.IsRing._.reflexive"
d2084 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2084 v9
du2084 v0 = coe du768 (coe d2050 v0)
name2086 = "Algebra.Structures.IsRing._.sym"
d2086 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v0)))))
name2088 = "Algebra.Structures.IsRing._.trans"
d2088 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v0)))))
name2092 = "Algebra.Structures.IsRing._.assoc"
d2092 v0 = coe d126 (coe d262 (coe d2052 v0))
name2094 = "Algebra.Structures.IsRing._.\8729-cong"
d2094 v0 = coe d128 (coe d262 (coe d2052 v0))
name2096 = "Algebra.Structures.IsRing._.identity"
d2096 v0 = coe d264 (coe d2052 v0)
name2098 = "Algebra.Structures.IsRing._.isSemigroup"
d2098 v0 = coe d262 (coe d2052 v0)
name2100 = "Algebra.Structures.IsRing.zero"
d2100 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2100 v2 v3 v4 v5 v6 v7 v9
du2100 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Data.Product.C30
      (coe d2126 erased erased v0 v1 v2 v3 v4 v5 erased v6)
      (coe d2130 erased erased v0 v1 v2 v3 v4 v5 erased v6)
name2110 = "Algebra.Structures.IsRing._._._\8718"
d2110 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2110 v2 v3 v9
du2110 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe MAlonzo.Code.Relation.Binary.C85 v0 v1
         (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v2))))))
name2112 = "Algebra.Structures.IsRing._._._\8764\10216_\10217_"
d2112 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2112 v2 v3 v9
du2112 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40
      (coe MAlonzo.Code.Relation.Binary.C85 v0 v1
         (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v2))))))
name2126 = "Algebra.Structures.IsRing._.zero\737"
d2126 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du2126 v2 v3 v4 v5 v6 v7 v9 v10
du2126 v0 v1 v2 v3 v4 v5 v6 v7
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du2112 v0 v1 v6 (coe v3 v5 v7) (coe v2 (coe v3 v5 v7) v5) v5
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
               (coe v2 (coe v3 v5 v7) v5)
               (coe v3 v5 v7))
            (coe MAlonzo.Code.Data.Product.d28
               (coe d264 (coe d588 (coe d746 (coe d2050 v6))))
               (coe v3 v5 v7)))
         (coe du2112 v0 v1 v6 (coe v2 (coe v3 v5 v7) v5)
            (coe v2 (coe v3 v5 v7)
               (coe v2 (coe v3 v5 v7) (coe v4 (coe v3 v5 v7))))
            v5
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                  (coe v3 v5 v7))
               (coe d128 (coe d262 (coe d588 (coe d746 (coe d2050 v6))))
                  (coe v3 v5 v7)
                  (coe v3 v5 v7)
                  v5
                  (coe v2 (coe v3 v5 v7) (coe v4 (coe v3 v5 v7))))
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                  (coe v2 (coe v3 v5 v7) (coe v4 (coe v3 v5 v7)))
                  v5
                  (coe MAlonzo.Code.Data.Product.d28
                     (coe d590 (coe d746 (coe d2050 v6)))
                     (coe v3 v5 v7))))
            (coe du2112 v0 v1 v6
               (coe v2 (coe v3 v5 v7)
                  (coe v2 (coe v3 v5 v7) (coe v4 (coe v3 v5 v7))))
               (coe v2 (coe v2 (coe v3 v5 v7) (coe v3 v5 v7))
                  (coe v4 (coe v3 v5 v7)))
               v5
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                     (coe v2 (coe v2 (coe v3 v5 v7) (coe v3 v5 v7))
                        (coe v4 (coe v3 v5 v7)))
                     (coe v2 (coe v3 v5 v7)
                        (coe v2 (coe v3 v5 v7) (coe v4 (coe v3 v5 v7)))))
                  (coe d126 (coe d262 (coe d588 (coe d746 (coe d2050 v6))))
                     (coe v3 v5 v7)
                     (coe v3 v5 v7)
                     (coe v4 (coe v3 v5 v7))))
               (coe du2112 v0 v1 v6
                  (coe v2 (coe v2 (coe v3 v5 v7) (coe v3 v5 v7))
                     (coe v4 (coe v3 v5 v7)))
                  (coe v2 (coe v3 (coe v2 v5 v5) v7) (coe v4 (coe v3 v5 v7)))
                  v5
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                        (coe v3 (coe v2 v5 v5) v7)
                        (coe v2 (coe v3 v5 v7) (coe v3 v5 v7))
                        (coe MAlonzo.Code.Data.Product.d28 (coe d2054 v6) v7 v5 v5))
                     (coe d128 (coe d262 (coe d588 (coe d746 (coe d2050 v6))))
                        (coe v2 (coe v3 v5 v7) (coe v3 v5 v7))
                        (coe v3 (coe v2 v5 v5) v7)
                        (coe v4 (coe v3 v5 v7))
                        (coe v4 (coe v3 v5 v7)))
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                        (coe v4 (coe v3 v5 v7))))
                  (coe du2112 v0 v1 v6
                     (coe v2 (coe v3 (coe v2 v5 v5) v7) (coe v4 (coe v3 v5 v7)))
                     (coe v2 (coe v3 v5 v7) (coe v4 (coe v3 v5 v7)))
                     v5
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Function.du176
                           (coe MAlonzo.Code.Data.Product.d28
                              (coe d264 (coe d588 (coe d746 (coe d2050 v6))))
                              v5)
                           (coe d128 (coe d262 (coe d2052 v6)) (coe v2 v5 v5) v5 v7 v7)
                           (coe MAlonzo.Code.Relation.Binary.Core.d516
                              (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                              v7))
                        (coe d128 (coe d262 (coe d588 (coe d746 (coe d2050 v6))))
                           (coe v3 (coe v2 v5 v5) v7)
                           (coe v3 v5 v7)
                           (coe v4 (coe v3 v5 v7))
                           (coe v4 (coe v3 v5 v7)))
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                           (coe v4 (coe v3 v5 v7))))
                     (coe du2112 v0 v1 v6
                        (coe v2 (coe v3 v5 v7) (coe v4 (coe v3 v5 v7)))
                        v5
                        v5
                        (coe MAlonzo.Code.Data.Product.d28
                           (coe d590 (coe d746 (coe d2050 v6)))
                           (coe v3 v5 v7))
                        (coe du2110 v0 v1 v6 v5)))))))
name2130 = "Algebra.Structures.IsRing._.zero\691"
d2130 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du2130 v2 v3 v4 v5 v6 v7 v9 v10
du2130 v0 v1 v2 v3 v4 v5 v6 v7
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du2112 v0 v1 v6 (coe v3 v7 v5) (coe v2 (coe v3 v7 v5) v5) v5
         (coe MAlonzo.Code.Function.du158
            (coe MAlonzo.Code.Relation.Binary.Core.d518
               (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
               (coe v2 (coe v3 v7 v5) v5)
               (coe v3 v7 v5))
            (coe MAlonzo.Code.Data.Product.d28
               (coe d264 (coe d588 (coe d746 (coe d2050 v6))))
               (coe v3 v7 v5)))
         (coe du2112 v0 v1 v6 (coe v2 (coe v3 v7 v5) v5)
            (coe v2 (coe v3 v7 v5)
               (coe v2 (coe v3 v7 v5) (coe v4 (coe v3 v7 v5))))
            v5
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Relation.Binary.Core.d516
                  (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                  (coe v3 v7 v5))
               (coe d128 (coe d262 (coe d588 (coe d746 (coe d2050 v6))))
                  (coe v3 v7 v5)
                  (coe v3 v7 v5)
                  v5
                  (coe v2 (coe v3 v7 v5) (coe v4 (coe v3 v7 v5))))
               (coe MAlonzo.Code.Relation.Binary.Core.d518
                  (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                  (coe v2 (coe v3 v7 v5) (coe v4 (coe v3 v7 v5)))
                  v5
                  (coe MAlonzo.Code.Data.Product.d28
                     (coe d590 (coe d746 (coe d2050 v6)))
                     (coe v3 v7 v5))))
            (coe du2112 v0 v1 v6
               (coe v2 (coe v3 v7 v5)
                  (coe v2 (coe v3 v7 v5) (coe v4 (coe v3 v7 v5))))
               (coe v2 (coe v2 (coe v3 v7 v5) (coe v3 v7 v5))
                  (coe v4 (coe v3 v7 v5)))
               v5
               (coe MAlonzo.Code.Function.du158
                  (coe MAlonzo.Code.Relation.Binary.Core.d518
                     (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                     (coe v2 (coe v2 (coe v3 v7 v5) (coe v3 v7 v5))
                        (coe v4 (coe v3 v7 v5)))
                     (coe v2 (coe v3 v7 v5)
                        (coe v2 (coe v3 v7 v5) (coe v4 (coe v3 v7 v5)))))
                  (coe d126 (coe d262 (coe d588 (coe d746 (coe d2050 v6))))
                     (coe v3 v7 v5)
                     (coe v3 v7 v5)
                     (coe v4 (coe v3 v7 v5))))
               (coe du2112 v0 v1 v6
                  (coe v2 (coe v2 (coe v3 v7 v5) (coe v3 v7 v5))
                     (coe v4 (coe v3 v7 v5)))
                  (coe v2 (coe v3 v7 (coe v2 v5 v5)) (coe v4 (coe v3 v7 v5)))
                  v5
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Relation.Binary.Core.d518
                        (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                        (coe v3 v7 (coe v2 v5 v5))
                        (coe v2 (coe v3 v7 v5) (coe v3 v7 v5))
                        (coe MAlonzo.Code.Data.Product.d26 (coe d2054 v6) v7 v5 v5))
                     (coe d128 (coe d262 (coe d588 (coe d746 (coe d2050 v6))))
                        (coe v2 (coe v3 v7 v5) (coe v3 v7 v5))
                        (coe v3 v7 (coe v2 v5 v5))
                        (coe v4 (coe v3 v7 v5))
                        (coe v4 (coe v3 v7 v5)))
                     (coe MAlonzo.Code.Relation.Binary.Core.d516
                        (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                        (coe v4 (coe v3 v7 v5))))
                  (coe du2112 v0 v1 v6
                     (coe v2 (coe v3 v7 (coe v2 v5 v5)) (coe v4 (coe v3 v7 v5)))
                     (coe v2 (coe v3 v7 v5) (coe v4 (coe v3 v7 v5)))
                     v5
                     (coe MAlonzo.Code.Function.du176
                        (coe MAlonzo.Code.Function.du176
                           (coe MAlonzo.Code.Relation.Binary.Core.d516
                              (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                              v7)
                           (coe d128 (coe d262 (coe d2052 v6)) v7 v7 (coe v2 v5 v5) v5)
                           (coe MAlonzo.Code.Data.Product.d28
                              (coe d264 (coe d588 (coe d746 (coe d2050 v6))))
                              v5))
                        (coe d128 (coe d262 (coe d588 (coe d746 (coe d2050 v6))))
                           (coe v3 v7 (coe v2 v5 v5))
                           (coe v3 v7 v5)
                           (coe v4 (coe v3 v7 v5))
                           (coe v4 (coe v3 v7 v5)))
                        (coe MAlonzo.Code.Relation.Binary.Core.d516
                           (coe d124 (coe d262 (coe d588 (coe d746 (coe d2050 v6)))))
                           (coe v4 (coe v3 v7 v5))))
                     (coe du2112 v0 v1 v6
                        (coe v2 (coe v3 v7 v5) (coe v4 (coe v3 v7 v5)))
                        v5
                        v5
                        (coe MAlonzo.Code.Data.Product.d28
                           (coe d590 (coe d746 (coe d2050 v6)))
                           (coe v3 v7 v5))
                        (coe du2110 v0 v1 v6 v5)))))))
name2134
  = "Algebra.Structures.IsRing.isSemiringWithoutAnnihilatingZero"
d2134 v0
  = coe C237
      (coe C71 (coe d262 (coe d588 (coe d746 (coe d2050 v0))))
         (coe MAlonzo.Code.Data.Product.d26
            (coe d264 (coe d588 (coe d746 (coe d2050 v0)))))
         (coe d748 (coe d2050 v0)))
      (coe d2052 v0)
      (coe d2054 v0)
name2136 = "Algebra.Structures.IsRing.isSemiring"
d2136 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2136 v2 v3 v4 v5 v6 v7 v9
du2136 v0 v1 v2 v3 v4 v5 v6
  = coe C261
      (coe C237
         (coe C71 (coe d262 (coe d588 (coe d746 (coe d2050 v6))))
            (coe MAlonzo.Code.Data.Product.d26
               (coe d264 (coe d588 (coe d746 (coe d2050 v6)))))
            (coe d748 (coe d2050 v6)))
         (coe d2052 v6)
         (coe d2054 v6))
      (coe du2100 v0 v1 v2 v3 v4 v5 v6)
name2140 = "Algebra.Structures.IsRing._.isNearSemiring"
d2140 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2140 v2 v3 v4 v5 v6 v7 v9
du2140 v0 v1 v2 v3 v4 v5 v6
  = coe du1462 v0 v1 v2 v5 (coe du2136 v0 v1 v2 v3 v4 v5 v6)
name2142 = "Algebra.Structures.IsRing._.isSemiringWithoutOne"
d2142 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2142 v2 v3 v4 v5 v6 v7 v9
du2142 v0 v1 v2 v3 v4 v5 v6
  = coe C199
      (coe d1246 (coe d1416 (coe du2136 v0 v1 v2 v3 v4 v5 v6)))
      (coe d262
         (coe d1248 (coe d1416 (coe du2136 v0 v1 v2 v3 v4 v5 v6))))
      (coe d1250 (coe d1416 (coe du2136 v0 v1 v2 v3 v4 v5 v6)))
      (coe d1418 (coe du2136 v0 v1 v2 v3 v4 v5 v6))
name2162 = "Algebra.Structures.IsCommutativeRing"
d2162 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()

data T2162 a0 a1 = C475 a0 a1
name2198 = "Algebra.Structures._.Commutative"
d2198 = erased
name2278 = "Algebra.Structures.IsCommutativeRing.isRing"
d2278 v0
  = case coe v0 of
        C475 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2280 = "Algebra.Structures.IsCommutativeRing.*-comm"
d2280 v0
  = case coe v0 of
        C475 v1 v2 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2284 = "Algebra.Structures.IsCommutativeRing._._-_"
d2284 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2284 v4 v6
du2284 v0 v1 = coe du2058 v0 v1
name2286 = "Algebra.Structures.IsCommutativeRing._.assoc"
d2286 v0 = coe d126 (coe d262 (coe d2052 (coe d2278 v0)))
name2288 = "Algebra.Structures.IsCommutativeRing._.\8729-cong"
d2288 v0 = coe d128 (coe d262 (coe d2052 (coe d2278 v0)))
name2290 = "Algebra.Structures.IsCommutativeRing._.identity"
d2290 v0 = coe d264 (coe d2052 (coe d2278 v0))
name2292 = "Algebra.Structures.IsCommutativeRing._.*-isMonoid"
d2292 v0 = coe d2052 (coe d2278 v0)
name2294 = "Algebra.Structures.IsCommutativeRing._.isSemigroup"
d2294 v0 = coe d262 (coe d2052 (coe d2278 v0))
name2296 = "Algebra.Structures.IsCommutativeRing._.assoc"
d2296 v0
  = coe d126
      (coe d262 (coe d588 (coe d746 (coe d2050 (coe d2278 v0)))))
name2298 = "Algebra.Structures.IsCommutativeRing._.comm"
d2298 v0 = coe d748 (coe d2050 (coe d2278 v0))
name2300 = "Algebra.Structures.IsCommutativeRing._.\8729-cong"
d2300 v0
  = coe d128
      (coe d262 (coe d588 (coe d746 (coe d2050 (coe d2278 v0)))))
name2302 = "Algebra.Structures.IsCommutativeRing._.identity"
d2302 v0
  = coe d264 (coe d588 (coe d746 (coe d2050 (coe d2278 v0))))
name2304
  = "Algebra.Structures.IsCommutativeRing._.+-isAbelianGroup"
d2304 v0 = coe d2050 (coe d2278 v0)
name2306
  = "Algebra.Structures.IsCommutativeRing._.isCommutativeMonoid"
d2306 v0
  = coe C71
      (coe d262 (coe d588 (coe d746 (coe d2050 (coe d2278 v0)))))
      (coe MAlonzo.Code.Data.Product.d26
         (coe d264 (coe d588 (coe d746 (coe d2050 (coe d2278 v0))))))
      (coe d748 (coe d2050 (coe d2278 v0)))
name2308 = "Algebra.Structures.IsCommutativeRing._.isGroup"
d2308 v0 = coe d746 (coe d2050 (coe d2278 v0))
name2310 = "Algebra.Structures.IsCommutativeRing._.isMonoid"
d2310 v0 = coe d588 (coe d746 (coe d2050 (coe d2278 v0)))
name2312 = "Algebra.Structures.IsCommutativeRing._.isSemigroup"
d2312 v0
  = coe d262 (coe d588 (coe d746 (coe d2050 (coe d2278 v0))))
name2314 = "Algebra.Structures.IsCommutativeRing._.\8315\185-cong"
d2314 v0 = coe d592 (coe d746 (coe d2050 (coe d2278 v0)))
name2316 = "Algebra.Structures.IsCommutativeRing._.inverse"
d2316 v0 = coe d590 (coe d746 (coe d2050 (coe d2278 v0)))
name2318 = "Algebra.Structures.IsCommutativeRing._.distrib"
d2318 v0 = coe d2054 (coe d2278 v0)
name2320 = "Algebra.Structures.IsCommutativeRing._.isEquivalence"
d2320 v0
  = coe d124
      (coe d262 (coe d588 (coe d746 (coe d2050 (coe d2278 v0)))))
name2322 = "Algebra.Structures.IsCommutativeRing._.isNearSemiring"
d2322 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2322 v2 v3 v4 v5 v6 v7 v9
du2322 v0 v1 v2 v3 v4 v5 v6
  = coe du2140 v0 v1 v2 v3 v4 v5 (coe d2278 v6)
name2324 = "Algebra.Structures.IsCommutativeRing._.isSemiring"
d2324 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2324 v2 v3 v4 v5 v6 v7 v9
du2324 v0 v1 v2 v3 v4 v5 v6
  = coe du2136 v0 v1 v2 v3 v4 v5 (coe d2278 v6)
name2326
  = "Algebra.Structures.IsCommutativeRing._.isSemiringWithoutAnnihilatingZero"
d2326 v0
  = coe C237
      (coe C71
         (coe d262 (coe d588 (coe d746 (coe d2050 (coe d2278 v0)))))
         (coe MAlonzo.Code.Data.Product.d26
            (coe d264 (coe d588 (coe d746 (coe d2050 (coe d2278 v0))))))
         (coe d748 (coe d2050 (coe d2278 v0))))
      (coe d2052 (coe d2278 v0))
      (coe d2054 (coe d2278 v0))
name2328
  = "Algebra.Structures.IsCommutativeRing._.isSemiringWithoutOne"
d2328 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2328 v2 v3 v4 v5 v6 v7 v9
du2328 v0 v1 v2 v3 v4 v5 v6
  = coe du2142 v0 v1 v2 v3 v4 v5 (coe d2278 v6)
name2330 = "Algebra.Structures.IsCommutativeRing._.refl"
d2330 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d124
         (coe d262 (coe d588 (coe d746 (coe d2050 (coe d2278 v0))))))
name2332 = "Algebra.Structures.IsCommutativeRing._.reflexive"
d2332 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2332 v9
du2332 v0 = coe du2084 (coe d2278 v0)
name2334 = "Algebra.Structures.IsCommutativeRing._.sym"
d2334 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d124
         (coe d262 (coe d588 (coe d746 (coe d2050 (coe d2278 v0))))))
name2336 = "Algebra.Structures.IsCommutativeRing._.trans"
d2336 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d124
         (coe d262 (coe d588 (coe d746 (coe d2050 (coe d2278 v0))))))
name2338 = "Algebra.Structures.IsCommutativeRing._.zero"
d2338 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2338 v2 v3 v4 v5 v6 v7 v9
du2338 v0 v1 v2 v3 v4 v5 v6
  = coe du2100 v0 v1 v2 v3 v4 v5 (coe d2278 v6)
name2340
  = "Algebra.Structures.IsCommutativeRing.isCommutativeSemiring"
d2340 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2340 v2 v3 v4 v5 v6 v7 v9
du2340 v0 v1 v2 v3 v4 v5 v6
  = coe C313
      (coe C71
         (coe d262 (coe d588 (coe d746 (coe d2050 (coe d2278 v6)))))
         (coe MAlonzo.Code.Data.Product.d26
            (coe d264 (coe d588 (coe d746 (coe d2050 (coe d2278 v6))))))
         (coe d748 (coe d2050 (coe d2278 v6))))
      (coe C71 (coe d262 (coe d2052 (coe d2278 v6)))
         (coe MAlonzo.Code.Data.Product.d26
            (coe d264 (coe d2052 (coe d2278 v6))))
         (coe d2280 v6))
      (coe MAlonzo.Code.Data.Product.d28 (coe d2054 (coe d2278 v6)))
      (coe MAlonzo.Code.Data.Product.d26
         (coe du2338 v0 v1 v2 v3 v4 v5 v6))
name2344
  = "Algebra.Structures.IsCommutativeRing._.*-isCommutativeMonoid"
d2344 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2344 v2 v3 v4 v5 v6 v7 v9
du2344 v0 v1 v2 v3 v4 v5 v6
  = coe d1768 (coe du2340 v0 v1 v2 v3 v4 v5 v6)
name2346
  = "Algebra.Structures.IsCommutativeRing._.isCommutativeSemiringWithoutOne"
d2346 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du2346 v2 v3 v4 v5 v6 v7 v8 v9
du2346 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du1912 v0 v1 v2 v3 v5 v6 (coe du2340 v0 v1 v2 v3 v4 v5 v7)
name2360 = "Algebra.Structures.IsLattice"
d2360 a0 a1 a2 a3 a4 a5 = ()

data T2360 a0 a1 a2 a3 a4 a5 a6 a7 = C539 a0 a1 a2 a3 a4 a5 a6 a7
name2386 = "Algebra.Structures._.Absorptive"
d2386 = erased
name2388 = "Algebra.Structures._.Associative"
d2388 = erased
name2390 = "Algebra.Structures._.Commutative"
d2390 = erased
name2482 = "Algebra.Structures.IsLattice.isEquivalence"
d2482 v0
  = case coe v0 of
        C539 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2484 = "Algebra.Structures.IsLattice.\8744-comm"
d2484 v0
  = case coe v0 of
        C539 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2486 = "Algebra.Structures.IsLattice.\8744-assoc"
d2486 v0
  = case coe v0 of
        C539 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2488 = "Algebra.Structures.IsLattice.\8744-cong"
d2488 v0
  = case coe v0 of
        C539 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2490 = "Algebra.Structures.IsLattice.\8743-comm"
d2490 v0
  = case coe v0 of
        C539 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2492 = "Algebra.Structures.IsLattice.\8743-assoc"
d2492 v0
  = case coe v0 of
        C539 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2494 = "Algebra.Structures.IsLattice.\8743-cong"
d2494 v0
  = case coe v0 of
        C539 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2496 = "Algebra.Structures.IsLattice.absorptive"
d2496 v0
  = case coe v0 of
        C539 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2500 = "Algebra.Structures.IsLattice._.refl"
d2500 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516 (coe d2482 v0)
name2502 = "Algebra.Structures.IsLattice._.reflexive"
d2502 v0 v1 v2 v3 v4 v5 v6 = du2502 v6
du2502 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d522 erased erased erased
      erased
      (coe d2482 v0)
name2504 = "Algebra.Structures.IsLattice._.sym"
d2504 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518 (coe d2482 v0)
name2506 = "Algebra.Structures.IsLattice._.trans"
d2506 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520 (coe d2482 v0)
name2520 = "Algebra.Structures.IsDistributiveLattice"
d2520 a0 a1 a2 a3 a4 a5 = ()

data T2520 a0 a1 = C573 a0 a1
name2540 = "Algebra.Structures._._DistributesOver\691_"
d2540 = erased
name2630 = "Algebra.Structures.IsDistributiveLattice.isLattice"
d2630 v0
  = case coe v0 of
        C573 v1 v2 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2632
  = "Algebra.Structures.IsDistributiveLattice.\8744-\8743-distrib\691"
d2632 v0
  = case coe v0 of
        C573 v1 v2 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2636 = "Algebra.Structures.IsDistributiveLattice._.absorptive"
d2636 v0 = coe d2496 (coe d2630 v0)
name2638
  = "Algebra.Structures.IsDistributiveLattice._.isEquivalence"
d2638 v0 = coe d2482 (coe d2630 v0)
name2640 = "Algebra.Structures.IsDistributiveLattice._.refl"
d2640 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d2482 (coe d2630 v0))
name2642 = "Algebra.Structures.IsDistributiveLattice._.reflexive"
d2642 v0 v1 v2 v3 v4 v5 v6 = du2642 v6
du2642 v0 = coe du2502 (coe d2630 v0)
name2644 = "Algebra.Structures.IsDistributiveLattice._.sym"
d2644 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d2482 (coe d2630 v0))
name2646 = "Algebra.Structures.IsDistributiveLattice._.trans"
d2646 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d2482 (coe d2630 v0))
name2648 = "Algebra.Structures.IsDistributiveLattice._.\8743-assoc"
d2648 v0 = coe d2492 (coe d2630 v0)
name2650 = "Algebra.Structures.IsDistributiveLattice._.\8743-comm"
d2650 v0 = coe d2490 (coe d2630 v0)
name2652 = "Algebra.Structures.IsDistributiveLattice._.\8743-cong"
d2652 v0 = coe d2494 (coe d2630 v0)
name2654 = "Algebra.Structures.IsDistributiveLattice._.\8744-assoc"
d2654 v0 = coe d2486 (coe d2630 v0)
name2656 = "Algebra.Structures.IsDistributiveLattice._.\8744-comm"
d2656 v0 = coe d2484 (coe d2630 v0)
name2658 = "Algebra.Structures.IsDistributiveLattice._.\8744-cong"
d2658 v0 = coe d2488 (coe d2630 v0)
name2678 = "Algebra.Structures.IsBooleanAlgebra"
d2678 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()

data T2678 a0 a1 a2 a3 = C605 a0 a1 a2 a3
name2734 = "Algebra.Structures._.RightInverse"
d2734 = erased
name2798
  = "Algebra.Structures.IsBooleanAlgebra.isDistributiveLattice"
d2798 v0
  = case coe v0 of
        C605 v1 v2 v3 v4 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2800
  = "Algebra.Structures.IsBooleanAlgebra.\8744-complement\691"
d2800 v0
  = case coe v0 of
        C605 v1 v2 v3 v4 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2802
  = "Algebra.Structures.IsBooleanAlgebra.\8743-complement\691"
d2802 v0
  = case coe v0 of
        C605 v1 v2 v3 v4 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2804 = "Algebra.Structures.IsBooleanAlgebra.\172-cong"
d2804 v0
  = case coe v0 of
        C605 v1 v2 v3 v4 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name2808 = "Algebra.Structures.IsBooleanAlgebra._.absorptive"
d2808 v0 = coe d2496 (coe d2630 (coe d2798 v0))
name2810 = "Algebra.Structures.IsBooleanAlgebra._.isEquivalence"
d2810 v0 = coe d2482 (coe d2630 (coe d2798 v0))
name2812 = "Algebra.Structures.IsBooleanAlgebra._.isLattice"
d2812 v0 = coe d2630 (coe d2798 v0)
name2814 = "Algebra.Structures.IsBooleanAlgebra._.refl"
d2814 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe d2482 (coe d2630 (coe d2798 v0)))
name2816 = "Algebra.Structures.IsBooleanAlgebra._.reflexive"
d2816 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du2816 v9
du2816 v0 = coe du2642 (coe d2798 v0)
name2818 = "Algebra.Structures.IsBooleanAlgebra._.sym"
d2818 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe d2482 (coe d2630 (coe d2798 v0)))
name2820 = "Algebra.Structures.IsBooleanAlgebra._.trans"
d2820 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe d2482 (coe d2630 (coe d2798 v0)))
name2822 = "Algebra.Structures.IsBooleanAlgebra._.\8743-assoc"
d2822 v0 = coe d2492 (coe d2630 (coe d2798 v0))
name2824 = "Algebra.Structures.IsBooleanAlgebra._.\8743-comm"
d2824 v0 = coe d2490 (coe d2630 (coe d2798 v0))
name2826 = "Algebra.Structures.IsBooleanAlgebra._.\8743-cong"
d2826 v0 = coe d2494 (coe d2630 (coe d2798 v0))
name2828 = "Algebra.Structures.IsBooleanAlgebra._.\8744-assoc"
d2828 v0 = coe d2486 (coe d2630 (coe d2798 v0))
name2830 = "Algebra.Structures.IsBooleanAlgebra._.\8744-comm"
d2830 v0 = coe d2484 (coe d2630 (coe d2798 v0))
name2832 = "Algebra.Structures.IsBooleanAlgebra._.\8744-cong"
d2832 v0 = coe d2488 (coe d2630 (coe d2798 v0))
name2834
  = "Algebra.Structures.IsBooleanAlgebra._.\8744-\8743-distrib\691"
d2834 v0 = coe d2632 (coe d2798 v0)