{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
name6 = "Algebra.Semigroup"
d6 a0 a1 = ()

data T6 a0 a1 a2 a3 = C5 a0 a1 a2 a3
name20 = "Algebra.Semigroup.Carrier"
d20 = erased
name22 = "Algebra.Semigroup._\8776_"
d22 = erased
name24 = "Algebra.Semigroup._\8729_"
d24 v0
  = case coe v0 of
        C5 v1 v2 v3 v4 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name26 = "Algebra.Semigroup.isSemigroup"
d26 v0
  = case coe v0 of
        C5 v1 v2 v3 v4 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name30 = "Algebra.Semigroup._.assoc"
d30 v0 = coe MAlonzo.Code.Algebra.Structures.d126 (coe d26 v0)
name32 = "Algebra.Semigroup._.isEquivalence"
d32 v0 = coe MAlonzo.Code.Algebra.Structures.d124 (coe d26 v0)
name34 = "Algebra.Semigroup._.refl"
d34 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124 (coe d26 v0))
name36 = "Algebra.Semigroup._.reflexive"
d36 v0 v1 v2 = du36 v2
du36 v0 = coe MAlonzo.Code.Algebra.Structures.du134 (coe d26 v0)
name38 = "Algebra.Semigroup._.sym"
d38 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124 (coe d26 v0))
name40 = "Algebra.Semigroup._.trans"
d40 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124 (coe d26 v0))
name42 = "Algebra.Semigroup._.\8729-cong"
d42 v0 = coe MAlonzo.Code.Algebra.Structures.d128 (coe d26 v0)
name44 = "Algebra.Semigroup.setoid"
d44 v0
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Algebra.Structures.d124 (coe d26 v0))
name50 = "Algebra.RawMonoid"
d50 a0 a1 = ()

data T50 a0 a1 a2 a3 = C19 a0 a1 a2 a3
name64 = "Algebra.RawMonoid.Carrier"
d64 = erased
name66 = "Algebra.RawMonoid._\8776_"
d66 = erased
name68 = "Algebra.RawMonoid._\8729_"
d68 v0
  = case coe v0 of
        C19 v1 v2 v3 v4 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name70 = "Algebra.RawMonoid.\949"
d70 v0
  = case coe v0 of
        C19 v1 v2 v3 v4 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name76 = "Algebra.Monoid"
d76 a0 a1 = ()

data T76 a0 a1 a2 a3 a4 = C37 a0 a1 a2 a3 a4
name92 = "Algebra.Monoid.Carrier"
d92 = erased
name94 = "Algebra.Monoid._\8776_"
d94 = erased
name96 = "Algebra.Monoid._\8729_"
d96 v0
  = case coe v0 of
        C37 v1 v2 v3 v4 v5 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name98 = "Algebra.Monoid.\949"
d98 v0
  = case coe v0 of
        C37 v1 v2 v3 v4 v5 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name100 = "Algebra.Monoid.isMonoid"
d100 v0
  = case coe v0 of
        C37 v1 v2 v3 v4 v5 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name104 = "Algebra.Monoid._.assoc"
d104 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d262 (coe d100 v0))
name106 = "Algebra.Monoid._.identity"
d106 v0 = coe MAlonzo.Code.Algebra.Structures.d264 (coe d100 v0)
name108 = "Algebra.Monoid._.isEquivalence"
d108 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d262 (coe d100 v0))
name110 = "Algebra.Monoid._.isSemigroup"
d110 v0 = coe MAlonzo.Code.Algebra.Structures.d262 (coe d100 v0)
name112 = "Algebra.Monoid._.refl"
d112 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262 (coe d100 v0)))
name114 = "Algebra.Monoid._.reflexive"
d114 v0 v1 v2 = du114 v2
du114 v0 = coe MAlonzo.Code.Algebra.Structures.du274 (coe d100 v0)
name116 = "Algebra.Monoid._.sym"
d116 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262 (coe d100 v0)))
name118 = "Algebra.Monoid._.trans"
d118 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262 (coe d100 v0)))
name120 = "Algebra.Monoid._.\8729-cong"
d120 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d262 (coe d100 v0))
name122 = "Algebra.Monoid.semigroup"
d122 v0
  = coe C5 erased erased (coe d96 v0)
      (coe MAlonzo.Code.Algebra.Structures.d262 (coe d100 v0))
name126 = "Algebra.Monoid._.setoid"
d126 v0
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262 (coe d100 v0)))
name128 = "Algebra.Monoid.rawMonoid"
d128 v0 = coe C19 erased erased (coe d96 v0) (coe d98 v0)
name134 = "Algebra.CommutativeMonoid"
d134 a0 a1 = ()

data T134 a0 a1 a2 a3 a4 = C61 a0 a1 a2 a3 a4
name150 = "Algebra.CommutativeMonoid.Carrier"
d150 = erased
name152 = "Algebra.CommutativeMonoid._\8776_"
d152 = erased
name154 = "Algebra.CommutativeMonoid._\8729_"
d154 v0
  = case coe v0 of
        C61 v1 v2 v3 v4 v5 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name156 = "Algebra.CommutativeMonoid.\949"
d156 v0
  = case coe v0 of
        C61 v1 v2 v3 v4 v5 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name158 = "Algebra.CommutativeMonoid.isCommutativeMonoid"
d158 v0
  = case coe v0 of
        C61 v1 v2 v3 v4 v5 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name162 = "Algebra.CommutativeMonoid._.assoc"
d162 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d406 (coe d158 v0))
name164 = "Algebra.CommutativeMonoid._.comm"
d164 v0 = coe MAlonzo.Code.Algebra.Structures.d410 (coe d158 v0)
name166 = "Algebra.CommutativeMonoid._.identity"
d166 v0 v1 v2 = du166 v2
du166 v0
  = coe MAlonzo.Code.Algebra.Structures.du428 erased erased
      (coe d154 v0)
      (coe d156 v0)
      (coe d158 v0)
name168 = "Algebra.CommutativeMonoid._.identity\737"
d168 v0 = coe MAlonzo.Code.Algebra.Structures.d408 (coe d158 v0)
name170 = "Algebra.CommutativeMonoid._.isEquivalence"
d170 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d406 (coe d158 v0))
name172 = "Algebra.CommutativeMonoid._.isMonoid"
d172 v0 v1 v2 = du172 v2
du172 v0
  = coe MAlonzo.Code.Algebra.Structures.du458 erased erased
      (coe d154 v0)
      (coe d156 v0)
      (coe d158 v0)
name174 = "Algebra.CommutativeMonoid._.isSemigroup"
d174 v0 = coe MAlonzo.Code.Algebra.Structures.d406 (coe d158 v0)
name176 = "Algebra.CommutativeMonoid._.refl"
d176 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406 (coe d158 v0)))
name178 = "Algebra.CommutativeMonoid._.reflexive"
d178 v0 v1 v2 = du178 v2
du178 v0 = coe MAlonzo.Code.Algebra.Structures.du420 (coe d158 v0)
name180 = "Algebra.CommutativeMonoid._.sym"
d180 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406 (coe d158 v0)))
name182 = "Algebra.CommutativeMonoid._.trans"
d182 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406 (coe d158 v0)))
name184 = "Algebra.CommutativeMonoid._.\8729-cong"
d184 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d406 (coe d158 v0))
name186 = "Algebra.CommutativeMonoid.monoid"
d186 v0 v1 v2 = du186 v2
du186 v0
  = coe C37 erased erased (coe d154 v0) (coe d156 v0) (coe du172 v0)
name190 = "Algebra.CommutativeMonoid._.rawMonoid"
d190 v0 v1 v2 = du190 v2
du190 v0
  = coe C19 erased erased (coe d96 (coe du186 v0))
      (coe d98 (coe du186 v0))
name192 = "Algebra.CommutativeMonoid._.semigroup"
d192 v0 v1 v2 = du192 v2
du192 v0
  = coe C5 erased erased (coe d96 (coe du186 v0))
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe d100 (coe du186 v0)))
name194 = "Algebra.CommutativeMonoid._.setoid"
d194 v0 v1 v2 = du194 v2
du194 v0
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe d100 (coe du186 v0))))
name200 = "Algebra.Group"
d200 a0 a1 = ()

data T200 a0 a1 a2 a3 a4 a5 = C81 a0 a1 a2 a3 a4 a5
name218 = "Algebra.Group.Carrier"
d218 = erased
name220 = "Algebra.Group._\8776_"
d220 = erased
name222 = "Algebra.Group._\8729_"
d222 v0
  = case coe v0 of
        C81 v1 v2 v3 v4 v5 v6 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name224 = "Algebra.Group.\949"
d224 v0
  = case coe v0 of
        C81 v1 v2 v3 v4 v5 v6 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name226 = "Algebra.Group._\8315\185"
d226 v0
  = case coe v0 of
        C81 v1 v2 v3 v4 v5 v6 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name228 = "Algebra.Group.isGroup"
d228 v0
  = case coe v0 of
        C81 v1 v2 v3 v4 v5 v6 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name232 = "Algebra.Group._._-_"
d232 v0 v1 v2 = du232 v2
du232 v0
  = coe MAlonzo.Code.Algebra.Structures.d614 erased erased erased
      erased
      (coe d222 v0)
      erased
      (coe d226 v0)
      erased
name234 = "Algebra.Group._.assoc"
d234 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0)))
name236 = "Algebra.Group._.identity"
d236 v0
  = coe MAlonzo.Code.Algebra.Structures.d264
      (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0))
name238 = "Algebra.Group._.inverse"
d238 v0 = coe MAlonzo.Code.Algebra.Structures.d590 (coe d228 v0)
name240 = "Algebra.Group._.isEquivalence"
d240 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0)))
name242 = "Algebra.Group._.isMonoid"
d242 v0 = coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0)
name244 = "Algebra.Group._.isSemigroup"
d244 v0
  = coe MAlonzo.Code.Algebra.Structures.d262
      (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0))
name246 = "Algebra.Group._.refl"
d246 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0))))
name248 = "Algebra.Group._.reflexive"
d248 v0 v1 v2 = du248 v2
du248 v0 = coe MAlonzo.Code.Algebra.Structures.du606 (coe d228 v0)
name250 = "Algebra.Group._.sym"
d250 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0))))
name252 = "Algebra.Group._.trans"
d252 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0))))
name254 = "Algebra.Group._.\8315\185-cong"
d254 v0 = coe MAlonzo.Code.Algebra.Structures.d592 (coe d228 v0)
name256 = "Algebra.Group._.\8729-cong"
d256 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0)))
name258 = "Algebra.Group.monoid"
d258 v0
  = coe C37 erased erased (coe d222 v0) (coe d224 v0)
      (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0))
name262 = "Algebra.Group._.rawMonoid"
d262 v0 = coe C19 erased erased (coe d222 v0) (coe d224 v0)
name264 = "Algebra.Group._.semigroup"
d264 v0
  = coe C5 erased erased (coe d222 v0)
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0)))
name266 = "Algebra.Group._.setoid"
d266 v0
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588 (coe d228 v0))))
name272 = "Algebra.AbelianGroup"
d272 a0 a1 = ()

data T272 a0 a1 a2 a3 a4 a5 = C103 a0 a1 a2 a3 a4 a5
name290 = "Algebra.AbelianGroup.Carrier"
d290 = erased
name292 = "Algebra.AbelianGroup._\8776_"
d292 = erased
name294 = "Algebra.AbelianGroup._\8729_"
d294 v0
  = case coe v0 of
        C103 v1 v2 v3 v4 v5 v6 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name296 = "Algebra.AbelianGroup.\949"
d296 v0
  = case coe v0 of
        C103 v1 v2 v3 v4 v5 v6 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name298 = "Algebra.AbelianGroup._\8315\185"
d298 v0
  = case coe v0 of
        C103 v1 v2 v3 v4 v5 v6 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name300 = "Algebra.AbelianGroup.isAbelianGroup"
d300 v0
  = case coe v0 of
        C103 v1 v2 v3 v4 v5 v6 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name304 = "Algebra.AbelianGroup._._-_"
d304 v0 v1 v2 = du304 v2
du304 v0
  = coe MAlonzo.Code.Algebra.Structures.du752 (coe d294 v0)
      (coe d298 v0)
name306 = "Algebra.AbelianGroup._.assoc"
d306 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0))))
name308 = "Algebra.AbelianGroup._.comm"
d308 v0 = coe MAlonzo.Code.Algebra.Structures.d748 (coe d300 v0)
name310 = "Algebra.AbelianGroup._.identity"
d310 v0
  = coe MAlonzo.Code.Algebra.Structures.d264
      (coe MAlonzo.Code.Algebra.Structures.d588
         (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0)))
name312 = "Algebra.AbelianGroup._.inverse"
d312 v0
  = coe MAlonzo.Code.Algebra.Structures.d590
      (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0))
name314 = "Algebra.AbelianGroup._.isCommutativeMonoid"
d314 v0
  = coe MAlonzo.Code.Algebra.Structures.C71
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0))))
      (coe MAlonzo.Code.Data.Product.d26
         (coe MAlonzo.Code.Algebra.Structures.d264
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0)))))
      (coe MAlonzo.Code.Algebra.Structures.d748 (coe d300 v0))
name316 = "Algebra.AbelianGroup._.isEquivalence"
d316 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0))))
name318 = "Algebra.AbelianGroup._.isGroup"
d318 v0 = coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0)
name320 = "Algebra.AbelianGroup._.isMonoid"
d320 v0
  = coe MAlonzo.Code.Algebra.Structures.d588
      (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0))
name322 = "Algebra.AbelianGroup._.isSemigroup"
d322 v0
  = coe MAlonzo.Code.Algebra.Structures.d262
      (coe MAlonzo.Code.Algebra.Structures.d588
         (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0)))
name324 = "Algebra.AbelianGroup._.refl"
d324 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0)))))
name326 = "Algebra.AbelianGroup._.reflexive"
d326 v0 v1 v2 = du326 v2
du326 v0 = coe MAlonzo.Code.Algebra.Structures.du768 (coe d300 v0)
name328 = "Algebra.AbelianGroup._.sym"
d328 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0)))))
name330 = "Algebra.AbelianGroup._.trans"
d330 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0)))))
name332 = "Algebra.AbelianGroup._.\8315\185-cong"
d332 v0
  = coe MAlonzo.Code.Algebra.Structures.d592
      (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0))
name334 = "Algebra.AbelianGroup._.\8729-cong"
d334 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0))))
name336 = "Algebra.AbelianGroup.group"
d336 v0
  = coe C81 erased erased (coe d294 v0) (coe d296 v0) (coe d298 v0)
      (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0))
name340 = "Algebra.AbelianGroup._.monoid"
d340 v0
  = coe C37 erased erased (coe d294 v0) (coe d296 v0)
      (coe MAlonzo.Code.Algebra.Structures.d588
         (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0)))
name342 = "Algebra.AbelianGroup._.rawMonoid"
d342 v0 = coe C19 erased erased (coe d294 v0) (coe d296 v0)
name344 = "Algebra.AbelianGroup._.semigroup"
d344 v0
  = coe C5 erased erased (coe d294 v0)
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0))))
name346 = "Algebra.AbelianGroup._.setoid"
d346 v0
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0)))))
name348 = "Algebra.AbelianGroup.commutativeMonoid"
d348 v0
  = coe C61 erased erased (coe d294 v0) (coe d296 v0)
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0))))
         (coe MAlonzo.Code.Data.Product.d26
            (coe MAlonzo.Code.Algebra.Structures.d264
               (coe MAlonzo.Code.Algebra.Structures.d588
                  (coe MAlonzo.Code.Algebra.Structures.d746 (coe d300 v0)))))
         (coe MAlonzo.Code.Algebra.Structures.d748 (coe d300 v0)))
name354 = "Algebra.NearSemiring"
d354 a0 a1 = ()

data T354 a0 a1 a2 a3 a4 a5 = C125 a0 a1 a2 a3 a4 a5
name372 = "Algebra.NearSemiring.Carrier"
d372 = erased
name374 = "Algebra.NearSemiring._\8776_"
d374 = erased
name376 = "Algebra.NearSemiring._+_"
d376 v0
  = case coe v0 of
        C125 v1 v2 v3 v4 v5 v6 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name378 = "Algebra.NearSemiring._*_"
d378 v0
  = case coe v0 of
        C125 v1 v2 v3 v4 v5 v6 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name380 = "Algebra.NearSemiring.0#"
d380 v0
  = case coe v0 of
        C125 v1 v2 v3 v4 v5 v6 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name382 = "Algebra.NearSemiring.isNearSemiring"
d382 v0
  = case coe v0 of
        C125 v1 v2 v3 v4 v5 v6 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name386 = "Algebra.NearSemiring._.assoc"
d386 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d912 (coe d382 v0))
name388 = "Algebra.NearSemiring._.\8729-cong"
d388 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d912 (coe d382 v0))
name390 = "Algebra.NearSemiring._.*-isSemigroup"
d390 v0 = coe MAlonzo.Code.Algebra.Structures.d912 (coe d382 v0)
name392 = "Algebra.NearSemiring._.assoc"
d392 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0)))
name394 = "Algebra.NearSemiring._.\8729-cong"
d394 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0)))
name396 = "Algebra.NearSemiring._.identity"
d396 v0
  = coe MAlonzo.Code.Algebra.Structures.d264
      (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0))
name398 = "Algebra.NearSemiring._.+-isMonoid"
d398 v0 = coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0)
name400 = "Algebra.NearSemiring._.isSemigroup"
d400 v0
  = coe MAlonzo.Code.Algebra.Structures.d262
      (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0))
name402 = "Algebra.NearSemiring._.distrib\691"
d402 v0 = coe MAlonzo.Code.Algebra.Structures.d914 (coe d382 v0)
name404 = "Algebra.NearSemiring._.isEquivalence"
d404 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0)))
name406 = "Algebra.NearSemiring._.refl"
d406 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0))))
name408 = "Algebra.NearSemiring._.reflexive"
d408 v0 v1 v2 = du408 v2
du408 v0 = coe MAlonzo.Code.Algebra.Structures.du932 (coe d382 v0)
name410 = "Algebra.NearSemiring._.sym"
d410 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0))))
name412 = "Algebra.NearSemiring._.trans"
d412 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0))))
name414 = "Algebra.NearSemiring._.zero\737"
d414 v0 = coe MAlonzo.Code.Algebra.Structures.d916 (coe d382 v0)
name416 = "Algebra.NearSemiring.+-monoid"
d416 v0
  = coe C37 erased erased (coe d376 v0) (coe d380 v0)
      (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0))
name420 = "Algebra.NearSemiring._.rawMonoid"
d420 v0 = coe C19 erased erased (coe d376 v0) (coe d380 v0)
name422 = "Algebra.NearSemiring._.semigroup"
d422 v0
  = coe C5 erased erased (coe d376 v0)
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0)))
name424 = "Algebra.NearSemiring._.setoid"
d424 v0
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d910 (coe d382 v0))))
name426 = "Algebra.NearSemiring.*-semigroup"
d426 v0
  = coe C5 erased erased (coe d378 v0)
      (coe MAlonzo.Code.Algebra.Structures.d912 (coe d382 v0))
name432 = "Algebra.SemiringWithoutOne"
d432 a0 a1 = ()

data T432 a0 a1 a2 a3 a4 a5 = C147 a0 a1 a2 a3 a4 a5
name450 = "Algebra.SemiringWithoutOne.Carrier"
d450 = erased
name452 = "Algebra.SemiringWithoutOne._\8776_"
d452 = erased
name454 = "Algebra.SemiringWithoutOne._+_"
d454 v0
  = case coe v0 of
        C147 v1 v2 v3 v4 v5 v6 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name456 = "Algebra.SemiringWithoutOne._*_"
d456 v0
  = case coe v0 of
        C147 v1 v2 v3 v4 v5 v6 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name458 = "Algebra.SemiringWithoutOne.0#"
d458 v0
  = case coe v0 of
        C147 v1 v2 v3 v4 v5 v6 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name460 = "Algebra.SemiringWithoutOne.isSemiringWithoutOne"
d460 v0
  = case coe v0 of
        C147 v1 v2 v3 v4 v5 v6 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name464 = "Algebra.SemiringWithoutOne._.assoc"
d464 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d1076 (coe d460 v0))
name466 = "Algebra.SemiringWithoutOne._.\8729-cong"
d466 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d1076 (coe d460 v0))
name468 = "Algebra.SemiringWithoutOne._.*-isSemigroup"
d468 v0 = coe MAlonzo.Code.Algebra.Structures.d1076 (coe d460 v0)
name470 = "Algebra.SemiringWithoutOne._.assoc"
d470 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1074 (coe d460 v0)))
name472 = "Algebra.SemiringWithoutOne._.comm"
d472 v0
  = coe MAlonzo.Code.Algebra.Structures.d410
      (coe MAlonzo.Code.Algebra.Structures.d1074 (coe d460 v0))
name474 = "Algebra.SemiringWithoutOne._.\8729-cong"
d474 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1074 (coe d460 v0)))
name476 = "Algebra.SemiringWithoutOne._.identity"
d476 v0 v1 v2 = du476 v2
du476 v0
  = coe MAlonzo.Code.Algebra.Structures.du1090 erased erased
      (coe d454 v0)
      (coe d458 v0)
      (coe d460 v0)
name478 = "Algebra.SemiringWithoutOne._.+-isCommutativeMonoid"
d478 v0 = coe MAlonzo.Code.Algebra.Structures.d1074 (coe d460 v0)
name480 = "Algebra.SemiringWithoutOne._.isMonoid"
d480 v0 v1 v2 = du480 v2
du480 v0
  = coe MAlonzo.Code.Algebra.Structures.du1092 erased erased
      (coe d454 v0)
      (coe d458 v0)
      (coe d460 v0)
name482 = "Algebra.SemiringWithoutOne._.isSemigroup"
d482 v0
  = coe MAlonzo.Code.Algebra.Structures.d406
      (coe MAlonzo.Code.Algebra.Structures.d1074 (coe d460 v0))
name484 = "Algebra.SemiringWithoutOne._.distrib"
d484 v0 = coe MAlonzo.Code.Algebra.Structures.d1078 (coe d460 v0)
name486 = "Algebra.SemiringWithoutOne._.isEquivalence"
d486 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1074 (coe d460 v0)))
name488 = "Algebra.SemiringWithoutOne._.isNearSemiring"
d488 v0 v1 v2 = du488 v2
du488 v0
  = coe MAlonzo.Code.Algebra.Structures.du1112 erased erased
      (coe d454 v0)
      (coe d458 v0)
      (coe d460 v0)
name490 = "Algebra.SemiringWithoutOne._.refl"
d490 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1074 (coe d460 v0))))
name492 = "Algebra.SemiringWithoutOne._.reflexive"
d492 v0 v1 v2 = du492 v2
du492 v0 = coe MAlonzo.Code.Algebra.Structures.du1100 (coe d460 v0)
name494 = "Algebra.SemiringWithoutOne._.sym"
d494 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1074 (coe d460 v0))))
name496 = "Algebra.SemiringWithoutOne._.trans"
d496 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1074 (coe d460 v0))))
name498 = "Algebra.SemiringWithoutOne._.zero"
d498 v0 = coe MAlonzo.Code.Algebra.Structures.d1080 (coe d460 v0)
name500 = "Algebra.SemiringWithoutOne.nearSemiring"
d500 v0 v1 v2 = du500 v2
du500 v0
  = coe C125 erased erased (coe d454 v0) (coe d456 v0) (coe d458 v0)
      (coe du488 v0)
name504 = "Algebra.SemiringWithoutOne._.*-semigroup"
d504 v0 v1 v2 = du504 v2
du504 v0
  = coe C5 erased erased (coe d378 (coe du500 v0))
      (coe MAlonzo.Code.Algebra.Structures.d912
         (coe d382 (coe du500 v0)))
name506 = "Algebra.SemiringWithoutOne._.+-monoid"
d506 v0 v1 v2 = du506 v2
du506 v0
  = coe C37 erased erased (coe d376 (coe du500 v0))
      (coe d380 (coe du500 v0))
      (coe MAlonzo.Code.Algebra.Structures.d910
         (coe d382 (coe du500 v0)))
name508 = "Algebra.SemiringWithoutOne._.rawMonoid"
d508 v0 v1 v2 = du508 v2
du508 v0
  = coe C19 erased erased (coe d376 (coe du500 v0))
      (coe d380 (coe du500 v0))
name510 = "Algebra.SemiringWithoutOne._.semigroup"
d510 v0 v1 v2 = du510 v2
du510 v0
  = coe C5 erased erased (coe d376 (coe du500 v0))
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d910
            (coe d382 (coe du500 v0))))
name512 = "Algebra.SemiringWithoutOne._.setoid"
d512 v0 v1 v2 = du512 v2
du512 v0
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d910
               (coe d382 (coe du500 v0)))))
name514 = "Algebra.SemiringWithoutOne.+-commutativeMonoid"
d514 v0
  = coe C61 erased erased (coe d454 v0) (coe d458 v0)
      (coe MAlonzo.Code.Algebra.Structures.d1074 (coe d460 v0))
name520 = "Algebra.SemiringWithoutAnnihilatingZero"
d520 a0 a1 = ()

data T520 a0 a1 a2 a3 a4 a5 a6 = C169 a0 a1 a2 a3 a4 a5 a6
name540 = "Algebra.SemiringWithoutAnnihilatingZero.Carrier"
d540 = erased
name542 = "Algebra.SemiringWithoutAnnihilatingZero._\8776_"
d542 = erased
name544 = "Algebra.SemiringWithoutAnnihilatingZero._+_"
d544 v0
  = case coe v0 of
        C169 v1 v2 v3 v4 v5 v6 v7 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name546 = "Algebra.SemiringWithoutAnnihilatingZero._*_"
d546 v0
  = case coe v0 of
        C169 v1 v2 v3 v4 v5 v6 v7 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name548 = "Algebra.SemiringWithoutAnnihilatingZero.0#"
d548 v0
  = case coe v0 of
        C169 v1 v2 v3 v4 v5 v6 v7 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name550 = "Algebra.SemiringWithoutAnnihilatingZero.1#"
d550 v0
  = case coe v0 of
        C169 v1 v2 v3 v4 v5 v6 v7 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name552
  = "Algebra.SemiringWithoutAnnihilatingZero.isSemiringWithoutAnnihilatingZero"
d552 v0
  = case coe v0 of
        C169 v1 v2 v3 v4 v5 v6 v7 -> coe v7
        _ -> coe MAlonzo.RTE.mazUnreachableError
name556 = "Algebra.SemiringWithoutAnnihilatingZero._.assoc"
d556 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d1248 (coe d552 v0)))
name558 = "Algebra.SemiringWithoutAnnihilatingZero._.\8729-cong"
d558 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d1248 (coe d552 v0)))
name560 = "Algebra.SemiringWithoutAnnihilatingZero._.identity"
d560 v0
  = coe MAlonzo.Code.Algebra.Structures.d264
      (coe MAlonzo.Code.Algebra.Structures.d1248 (coe d552 v0))
name562 = "Algebra.SemiringWithoutAnnihilatingZero._.*-isMonoid"
d562 v0 = coe MAlonzo.Code.Algebra.Structures.d1248 (coe d552 v0)
name564 = "Algebra.SemiringWithoutAnnihilatingZero._.isSemigroup"
d564 v0
  = coe MAlonzo.Code.Algebra.Structures.d262
      (coe MAlonzo.Code.Algebra.Structures.d1248 (coe d552 v0))
name566 = "Algebra.SemiringWithoutAnnihilatingZero._.assoc"
d566 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0)))
name568 = "Algebra.SemiringWithoutAnnihilatingZero._.comm"
d568 v0
  = coe MAlonzo.Code.Algebra.Structures.d410
      (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0))
name570 = "Algebra.SemiringWithoutAnnihilatingZero._.\8729-cong"
d570 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0)))
name572 = "Algebra.SemiringWithoutAnnihilatingZero._.identity"
d572 v0 v1 v2 = du572 v2
du572 v0
  = coe MAlonzo.Code.Algebra.Structures.du1260 erased erased
      (coe d544 v0)
      (coe d548 v0)
      (coe d552 v0)
name574
  = "Algebra.SemiringWithoutAnnihilatingZero._.+-isCommutativeMonoid"
d574 v0 = coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0)
name576 = "Algebra.SemiringWithoutAnnihilatingZero._.isMonoid"
d576 v0 v1 v2 = du576 v2
du576 v0
  = coe MAlonzo.Code.Algebra.Structures.du1262 erased erased
      (coe d544 v0)
      (coe d548 v0)
      (coe d552 v0)
name578 = "Algebra.SemiringWithoutAnnihilatingZero._.isSemigroup"
d578 v0
  = coe MAlonzo.Code.Algebra.Structures.d406
      (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0))
name580 = "Algebra.SemiringWithoutAnnihilatingZero._.distrib"
d580 v0 = coe MAlonzo.Code.Algebra.Structures.d1250 (coe d552 v0)
name582 = "Algebra.SemiringWithoutAnnihilatingZero._.isEquivalence"
d582 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0)))
name584 = "Algebra.SemiringWithoutAnnihilatingZero._.refl"
d584 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0))))
name586 = "Algebra.SemiringWithoutAnnihilatingZero._.reflexive"
d586 v0 v1 v2 = du586 v2
du586 v0 = coe MAlonzo.Code.Algebra.Structures.du1270 (coe d552 v0)
name588 = "Algebra.SemiringWithoutAnnihilatingZero._.sym"
d588 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0))))
name590 = "Algebra.SemiringWithoutAnnihilatingZero._.trans"
d590 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0))))
name592
  = "Algebra.SemiringWithoutAnnihilatingZero.+-commutativeMonoid"
d592 v0
  = coe C61 erased erased (coe d544 v0) (coe d548 v0)
      (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0))
name596 = "Algebra.SemiringWithoutAnnihilatingZero._.monoid"
d596 v0 v1 v2 = du596 v2
du596 v0
  = coe du186
      (coe C61 erased erased (coe d544 v0) (coe d548 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0)))
name598 = "Algebra.SemiringWithoutAnnihilatingZero._.rawMonoid"
d598 v0 v1 v2 = du598 v2
du598 v0
  = coe du190
      (coe C61 erased erased (coe d544 v0) (coe d548 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0)))
name600 = "Algebra.SemiringWithoutAnnihilatingZero._.semigroup"
d600 v0 v1 v2 = du600 v2
du600 v0
  = coe du192
      (coe C61 erased erased (coe d544 v0) (coe d548 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0)))
name602 = "Algebra.SemiringWithoutAnnihilatingZero._.setoid"
d602 v0 v1 v2 = du602 v2
du602 v0
  = coe du194
      (coe C61 erased erased (coe d544 v0) (coe d548 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1246 (coe d552 v0)))
name604 = "Algebra.SemiringWithoutAnnihilatingZero.*-monoid"
d604 v0
  = coe C37 erased erased (coe d546 v0) (coe d550 v0)
      (coe MAlonzo.Code.Algebra.Structures.d1248 (coe d552 v0))
name608 = "Algebra.SemiringWithoutAnnihilatingZero._.rawMonoid"
d608 v0 = coe C19 erased erased (coe d546 v0) (coe d550 v0)
name610 = "Algebra.SemiringWithoutAnnihilatingZero._.semigroup"
d610 v0
  = coe C5 erased erased (coe d546 v0)
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d1248 (coe d552 v0)))
name616 = "Algebra.Semiring"
d616 a0 a1 = ()

data T616 a0 a1 a2 a3 a4 a5 a6 = C193 a0 a1 a2 a3 a4 a5 a6
name636 = "Algebra.Semiring.Carrier"
d636 = erased
name638 = "Algebra.Semiring._\8776_"
d638 = erased
name640 = "Algebra.Semiring._+_"
d640 v0
  = case coe v0 of
        C193 v1 v2 v3 v4 v5 v6 v7 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name642 = "Algebra.Semiring._*_"
d642 v0
  = case coe v0 of
        C193 v1 v2 v3 v4 v5 v6 v7 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name644 = "Algebra.Semiring.0#"
d644 v0
  = case coe v0 of
        C193 v1 v2 v3 v4 v5 v6 v7 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name646 = "Algebra.Semiring.1#"
d646 v0
  = case coe v0 of
        C193 v1 v2 v3 v4 v5 v6 v7 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name648 = "Algebra.Semiring.isSemiring"
d648 v0
  = case coe v0 of
        C193 v1 v2 v3 v4 v5 v6 v7 -> coe v7
        _ -> coe MAlonzo.RTE.mazUnreachableError
name652 = "Algebra.Semiring._.assoc"
d652 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d1248
            (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))))
name654 = "Algebra.Semiring._.\8729-cong"
d654 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d1248
            (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))))
name656 = "Algebra.Semiring._.identity"
d656 v0
  = coe MAlonzo.Code.Algebra.Structures.d264
      (coe MAlonzo.Code.Algebra.Structures.d1248
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
name658 = "Algebra.Semiring._.*-isMonoid"
d658 v0
  = coe MAlonzo.Code.Algebra.Structures.d1248
      (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))
name660 = "Algebra.Semiring._.isSemigroup"
d660 v0
  = coe MAlonzo.Code.Algebra.Structures.d262
      (coe MAlonzo.Code.Algebra.Structures.d1248
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
name662 = "Algebra.Semiring._.assoc"
d662 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1246
            (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))))
name664 = "Algebra.Semiring._.comm"
d664 v0
  = coe MAlonzo.Code.Algebra.Structures.d410
      (coe MAlonzo.Code.Algebra.Structures.d1246
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
name666 = "Algebra.Semiring._.\8729-cong"
d666 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1246
            (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))))
name668 = "Algebra.Semiring._.identity"
d668 v0 v1 v2 = du668 v2
du668 v0
  = coe MAlonzo.Code.Algebra.Structures.du1438 erased erased
      (coe d640 v0)
      (coe d644 v0)
      (coe d648 v0)
name670 = "Algebra.Semiring._.+-isCommutativeMonoid"
d670 v0
  = coe MAlonzo.Code.Algebra.Structures.d1246
      (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))
name672 = "Algebra.Semiring._.isMonoid"
d672 v0 v1 v2 = du672 v2
du672 v0
  = coe MAlonzo.Code.Algebra.Structures.du1442 erased erased
      (coe d640 v0)
      (coe d644 v0)
      (coe d648 v0)
name674 = "Algebra.Semiring._.isSemigroup"
d674 v0
  = coe MAlonzo.Code.Algebra.Structures.d406
      (coe MAlonzo.Code.Algebra.Structures.d1246
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
name676 = "Algebra.Semiring._.distrib"
d676 v0
  = coe MAlonzo.Code.Algebra.Structures.d1250
      (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))
name678 = "Algebra.Semiring._.isEquivalence"
d678 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1246
            (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))))
name680 = "Algebra.Semiring._.isNearSemiring"
d680 v0 v1 v2 = du680 v2
du680 v0
  = coe MAlonzo.Code.Algebra.Structures.du1462 erased erased
      (coe d640 v0)
      (coe d644 v0)
      (coe d648 v0)
name682 = "Algebra.Semiring._.isSemiringWithoutAnnihilatingZero"
d682 v0 = coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)
name684 = "Algebra.Semiring._.isSemiringWithoutOne"
d684 v0
  = coe MAlonzo.Code.Algebra.Structures.C199
      (coe MAlonzo.Code.Algebra.Structures.d1246
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d1248
            (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))))
      (coe MAlonzo.Code.Algebra.Structures.d1250
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
      (coe MAlonzo.Code.Algebra.Structures.d1418 (coe d648 v0))
name686 = "Algebra.Semiring._.refl"
d686 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1246
               (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))))
name688 = "Algebra.Semiring._.reflexive"
d688 v0 v1 v2 = du688 v2
du688 v0 = coe MAlonzo.Code.Algebra.Structures.du1452 (coe d648 v0)
name690 = "Algebra.Semiring._.sym"
d690 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1246
               (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))))
name692 = "Algebra.Semiring._.trans"
d692 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1246
               (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))))
name694 = "Algebra.Semiring._.zero"
d694 v0 = coe MAlonzo.Code.Algebra.Structures.d1418 (coe d648 v0)
name696 = "Algebra.Semiring.semiringWithoutAnnihilatingZero"
d696 v0
  = coe C169 erased erased (coe d640 v0) (coe d642 v0) (coe d644 v0)
      (coe d646 v0)
      (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))
name700 = "Algebra.Semiring._.*-monoid"
d700 v0
  = coe C37 erased erased (coe d642 v0) (coe d646 v0)
      (coe MAlonzo.Code.Algebra.Structures.d1248
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
name702 = "Algebra.Semiring._.rawMonoid"
d702 v0 = coe C19 erased erased (coe d642 v0) (coe d646 v0)
name704 = "Algebra.Semiring._.semigroup"
d704 v0
  = coe C5 erased erased (coe d642 v0)
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d1248
            (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))))
name706 = "Algebra.Semiring._.+-commutativeMonoid"
d706 v0
  = coe C61 erased erased (coe d640 v0) (coe d644 v0)
      (coe MAlonzo.Code.Algebra.Structures.d1246
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
name708 = "Algebra.Semiring._.monoid"
d708 v0 v1 v2 = du708 v2
du708 v0
  = coe du596
      (coe C169 erased erased (coe d640 v0) (coe d642 v0) (coe d644 v0)
         (coe d646 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
name710 = "Algebra.Semiring._.rawMonoid"
d710 v0 v1 v2 = du710 v2
du710 v0
  = coe du598
      (coe C169 erased erased (coe d640 v0) (coe d642 v0) (coe d644 v0)
         (coe d646 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
name712 = "Algebra.Semiring._.semigroup"
d712 v0 v1 v2 = du712 v2
du712 v0
  = coe du600
      (coe C169 erased erased (coe d640 v0) (coe d642 v0) (coe d644 v0)
         (coe d646 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
name714 = "Algebra.Semiring._.setoid"
d714 v0 v1 v2 = du714 v2
du714 v0
  = coe du602
      (coe C169 erased erased (coe d640 v0) (coe d642 v0) (coe d644 v0)
         (coe d646 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
name716 = "Algebra.Semiring.semiringWithoutOne"
d716 v0
  = coe C147 erased erased (coe d640 v0) (coe d642 v0) (coe d644 v0)
      (coe MAlonzo.Code.Algebra.Structures.C199
         (coe MAlonzo.Code.Algebra.Structures.d1246
            (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d1248
               (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))))
         (coe MAlonzo.Code.Algebra.Structures.d1250
            (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
         (coe MAlonzo.Code.Algebra.Structures.d1418 (coe d648 v0)))
name720 = "Algebra.Semiring._.nearSemiring"
d720 v0 v1 v2 = du720 v2
du720 v0
  = coe du500
      (coe C147 erased erased (coe d640 v0) (coe d642 v0) (coe d644 v0)
         (coe MAlonzo.Code.Algebra.Structures.C199
            (coe MAlonzo.Code.Algebra.Structures.d1246
               (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
            (coe MAlonzo.Code.Algebra.Structures.d262
               (coe MAlonzo.Code.Algebra.Structures.d1248
                  (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0))))
            (coe MAlonzo.Code.Algebra.Structures.d1250
               (coe MAlonzo.Code.Algebra.Structures.d1416 (coe d648 v0)))
            (coe MAlonzo.Code.Algebra.Structures.d1418 (coe d648 v0))))
name726 = "Algebra.CommutativeSemiringWithoutOne"
d726 a0 a1 = ()

data T726 a0 a1 a2 a3 a4 a5 = C217 a0 a1 a2 a3 a4 a5
name744 = "Algebra.CommutativeSemiringWithoutOne.Carrier"
d744 = erased
name746 = "Algebra.CommutativeSemiringWithoutOne._\8776_"
d746 = erased
name748 = "Algebra.CommutativeSemiringWithoutOne._+_"
d748 v0
  = case coe v0 of
        C217 v1 v2 v3 v4 v5 v6 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name750 = "Algebra.CommutativeSemiringWithoutOne._*_"
d750 v0
  = case coe v0 of
        C217 v1 v2 v3 v4 v5 v6 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name752 = "Algebra.CommutativeSemiringWithoutOne.0#"
d752 v0
  = case coe v0 of
        C217 v1 v2 v3 v4 v5 v6 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name754
  = "Algebra.CommutativeSemiringWithoutOne.isCommutativeSemiringWithoutOne"
d754 v0
  = case coe v0 of
        C217 v1 v2 v3 v4 v5 v6 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name758 = "Algebra.CommutativeSemiringWithoutOne._.assoc"
d758 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d1076
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name760 = "Algebra.CommutativeSemiringWithoutOne._.*-comm"
d760 v0 = coe MAlonzo.Code.Algebra.Structures.d1592 (coe d754 v0)
name762 = "Algebra.CommutativeSemiringWithoutOne._.\8729-cong"
d762 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d1076
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name764 = "Algebra.CommutativeSemiringWithoutOne._.*-isSemigroup"
d764 v0
  = coe MAlonzo.Code.Algebra.Structures.d1076
      (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0))
name766 = "Algebra.CommutativeSemiringWithoutOne._.assoc"
d766 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1074
            (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0))))
name768 = "Algebra.CommutativeSemiringWithoutOne._.comm"
d768 v0
  = coe MAlonzo.Code.Algebra.Structures.d410
      (coe MAlonzo.Code.Algebra.Structures.d1074
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name770 = "Algebra.CommutativeSemiringWithoutOne._.\8729-cong"
d770 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1074
            (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0))))
name772 = "Algebra.CommutativeSemiringWithoutOne._.identity"
d772 v0 v1 v2 = du772 v2
du772 v0
  = coe MAlonzo.Code.Algebra.Structures.du1608 erased erased
      (coe d748 v0)
      (coe d752 v0)
      (coe d754 v0)
name774
  = "Algebra.CommutativeSemiringWithoutOne._.+-isCommutativeMonoid"
d774 v0
  = coe MAlonzo.Code.Algebra.Structures.d1074
      (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0))
name776 = "Algebra.CommutativeSemiringWithoutOne._.isMonoid"
d776 v0 v1 v2 = du776 v2
du776 v0
  = coe MAlonzo.Code.Algebra.Structures.du1612 erased erased
      (coe d748 v0)
      (coe d752 v0)
      (coe d754 v0)
name778 = "Algebra.CommutativeSemiringWithoutOne._.isSemigroup"
d778 v0
  = coe MAlonzo.Code.Algebra.Structures.d406
      (coe MAlonzo.Code.Algebra.Structures.d1074
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name780 = "Algebra.CommutativeSemiringWithoutOne._.distrib"
d780 v0
  = coe MAlonzo.Code.Algebra.Structures.d1078
      (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0))
name782 = "Algebra.CommutativeSemiringWithoutOne._.isEquivalence"
d782 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d406
         (coe MAlonzo.Code.Algebra.Structures.d1074
            (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0))))
name784 = "Algebra.CommutativeSemiringWithoutOne._.isNearSemiring"
d784 v0 v1 v2 = du784 v2
du784 v0
  = coe MAlonzo.Code.Algebra.Structures.du1620 erased erased
      (coe d748 v0)
      (coe d752 v0)
      (coe d754 v0)
name786
  = "Algebra.CommutativeSemiringWithoutOne._.isSemiringWithoutOne"
d786 v0 = coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)
name788 = "Algebra.CommutativeSemiringWithoutOne._.refl"
d788 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1074
               (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))))
name790 = "Algebra.CommutativeSemiringWithoutOne._.reflexive"
d790 v0 v1 v2 = du790 v2
du790 v0 = coe MAlonzo.Code.Algebra.Structures.du1624 (coe d754 v0)
name792 = "Algebra.CommutativeSemiringWithoutOne._.sym"
d792 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1074
               (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))))
name794 = "Algebra.CommutativeSemiringWithoutOne._.trans"
d794 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d406
            (coe MAlonzo.Code.Algebra.Structures.d1074
               (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))))
name796 = "Algebra.CommutativeSemiringWithoutOne._.zero"
d796 v0
  = coe MAlonzo.Code.Algebra.Structures.d1080
      (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0))
name798
  = "Algebra.CommutativeSemiringWithoutOne.semiringWithoutOne"
d798 v0
  = coe C147 erased erased (coe d748 v0) (coe d750 v0) (coe d752 v0)
      (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0))
name802 = "Algebra.CommutativeSemiringWithoutOne._.*-semigroup"
d802 v0 v1 v2 = du802 v2
du802 v0
  = coe du504
      (coe C147 erased erased (coe d748 v0) (coe d750 v0) (coe d752 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name804
  = "Algebra.CommutativeSemiringWithoutOne._.+-commutativeMonoid"
d804 v0
  = coe C61 erased erased (coe d748 v0) (coe d752 v0)
      (coe MAlonzo.Code.Algebra.Structures.d1074
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name806 = "Algebra.CommutativeSemiringWithoutOne._.+-monoid"
d806 v0 v1 v2 = du806 v2
du806 v0
  = coe du506
      (coe C147 erased erased (coe d748 v0) (coe d750 v0) (coe d752 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name808 = "Algebra.CommutativeSemiringWithoutOne._.rawMonoid"
d808 v0 v1 v2 = du808 v2
du808 v0
  = coe du508
      (coe C147 erased erased (coe d748 v0) (coe d750 v0) (coe d752 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name810 = "Algebra.CommutativeSemiringWithoutOne._.semigroup"
d810 v0 v1 v2 = du810 v2
du810 v0
  = coe du510
      (coe C147 erased erased (coe d748 v0) (coe d750 v0) (coe d752 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name812 = "Algebra.CommutativeSemiringWithoutOne._.nearSemiring"
d812 v0 v1 v2 = du812 v2
du812 v0
  = coe du500
      (coe C147 erased erased (coe d748 v0) (coe d750 v0) (coe d752 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name814 = "Algebra.CommutativeSemiringWithoutOne._.setoid"
d814 v0 v1 v2 = du814 v2
du814 v0
  = coe du512
      (coe C147 erased erased (coe d748 v0) (coe d750 v0) (coe d752 v0)
         (coe MAlonzo.Code.Algebra.Structures.d1590 (coe d754 v0)))
name820 = "Algebra.CommutativeSemiring"
d820 a0 a1 = ()

data T820 a0 a1 a2 a3 a4 a5 a6 = C239 a0 a1 a2 a3 a4 a5 a6
name840 = "Algebra.CommutativeSemiring.Carrier"
d840 = erased
name842 = "Algebra.CommutativeSemiring._\8776_"
d842 = erased
name844 = "Algebra.CommutativeSemiring._+_"
d844 v0
  = case coe v0 of
        C239 v1 v2 v3 v4 v5 v6 v7 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name846 = "Algebra.CommutativeSemiring._*_"
d846 v0
  = case coe v0 of
        C239 v1 v2 v3 v4 v5 v6 v7 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name848 = "Algebra.CommutativeSemiring.0#"
d848 v0
  = case coe v0 of
        C239 v1 v2 v3 v4 v5 v6 v7 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name850 = "Algebra.CommutativeSemiring.1#"
d850 v0
  = case coe v0 of
        C239 v1 v2 v3 v4 v5 v6 v7 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name852 = "Algebra.CommutativeSemiring.isCommutativeSemiring"
d852 v0
  = case coe v0 of
        C239 v1 v2 v3 v4 v5 v6 v7 -> coe v7
        _ -> coe MAlonzo.RTE.mazUnreachableError
name856 = "Algebra.CommutativeSemiring._.assoc"
d856 v0 v1 v2 = du856 v2
du856 v0
  = coe MAlonzo.Code.Algebra.Structures.du1874 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name858 = "Algebra.CommutativeSemiring._.comm"
d858 v0
  = coe MAlonzo.Code.Algebra.Structures.d410
      (coe MAlonzo.Code.Algebra.Structures.d1768 (coe d852 v0))
name860 = "Algebra.CommutativeSemiring._.\8729-cong"
d860 v0 v1 v2 = du860 v2
du860 v0
  = coe MAlonzo.Code.Algebra.Structures.du1876 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name862 = "Algebra.CommutativeSemiring._.identity"
d862 v0 v1 v2 = du862 v2
du862 v0
  = coe MAlonzo.Code.Algebra.Structures.du1878 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name864 = "Algebra.CommutativeSemiring._.*-isCommutativeMonoid"
d864 v0 = coe MAlonzo.Code.Algebra.Structures.d1768 (coe d852 v0)
name866 = "Algebra.CommutativeSemiring._.*-isMonoid"
d866 v0 v1 v2 = du866 v2
du866 v0
  = coe MAlonzo.Code.Algebra.Structures.du1880 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name868 = "Algebra.CommutativeSemiring._.isSemigroup"
d868 v0 v1 v2 = du868 v2
du868 v0
  = coe MAlonzo.Code.Algebra.Structures.du1882 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name870 = "Algebra.CommutativeSemiring._.assoc"
d870 v0 v1 v2 = du870 v2
du870 v0
  = coe MAlonzo.Code.Algebra.Structures.du1884 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name872 = "Algebra.CommutativeSemiring._.comm"
d872 v0 v1 v2 = du872 v2
du872 v0
  = coe MAlonzo.Code.Algebra.Structures.du1886 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name874 = "Algebra.CommutativeSemiring._.\8729-cong"
d874 v0 v1 v2 = du874 v2
du874 v0
  = coe MAlonzo.Code.Algebra.Structures.du1888 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name876 = "Algebra.CommutativeSemiring._.identity"
d876 v0 v1 v2 = du876 v2
du876 v0
  = coe MAlonzo.Code.Algebra.Structures.du1890 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name878 = "Algebra.CommutativeSemiring._.+-isCommutativeMonoid"
d878 v0 = coe MAlonzo.Code.Algebra.Structures.d1766 (coe d852 v0)
name880 = "Algebra.CommutativeSemiring._.isMonoid"
d880 v0 v1 v2 = du880 v2
du880 v0
  = coe MAlonzo.Code.Algebra.Structures.du1892 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name882 = "Algebra.CommutativeSemiring._.isSemigroup"
d882 v0 v1 v2 = du882 v2
du882 v0
  = coe MAlonzo.Code.Algebra.Structures.du1894 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name884 = "Algebra.CommutativeSemiring._.distrib"
d884 v0 v1 v2 = du884 v2
du884 v0
  = coe MAlonzo.Code.Algebra.Structures.du1846 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d852 v0)
name886 = "Algebra.CommutativeSemiring._.distrib\691"
d886 v0 = coe MAlonzo.Code.Algebra.Structures.d1770 (coe d852 v0)
name888
  = "Algebra.CommutativeSemiring._.isCommutativeSemiringWithoutOne"
d888 v0 v1 v2 = du888 v2
du888 v0
  = coe MAlonzo.Code.Algebra.Structures.du1912 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name890 = "Algebra.CommutativeSemiring._.isEquivalence"
d890 v0 v1 v2 = du890 v2
du890 v0
  = coe MAlonzo.Code.Algebra.Structures.du1896 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name892 = "Algebra.CommutativeSemiring._.isNearSemiring"
d892 v0 v1 v2 = du892 v2
du892 v0
  = coe MAlonzo.Code.Algebra.Structures.du1898 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name894 = "Algebra.CommutativeSemiring._.isSemiring"
d894 v0 v1 v2 = du894 v2
du894 v0
  = coe MAlonzo.Code.Algebra.Structures.du1870 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name896
  = "Algebra.CommutativeSemiring._.isSemiringWithoutAnnihilatingZero"
d896 v0 v1 v2 = du896 v2
du896 v0
  = coe MAlonzo.Code.Algebra.Structures.du1900 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name898 = "Algebra.CommutativeSemiring._.isSemiringWithoutOne"
d898 v0 v1 v2 = du898 v2
du898 v0
  = coe MAlonzo.Code.Algebra.Structures.du1902 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name900 = "Algebra.CommutativeSemiring._.refl"
d900 v0 v1 v2 = du900 v2
du900 v0
  = coe MAlonzo.Code.Algebra.Structures.du1904 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name902 = "Algebra.CommutativeSemiring._.reflexive"
d902 v0 v1 v2 = du902 v2
du902 v0
  = coe MAlonzo.Code.Algebra.Structures.du1906 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name904 = "Algebra.CommutativeSemiring._.sym"
d904 v0 v1 v2 = du904 v2
du904 v0
  = coe MAlonzo.Code.Algebra.Structures.du1908 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name906 = "Algebra.CommutativeSemiring._.trans"
d906 v0 v1 v2 = du906 v2
du906 v0
  = coe MAlonzo.Code.Algebra.Structures.du1910 erased erased
      (coe d844 v0)
      (coe d846 v0)
      (coe d848 v0)
      (coe d850 v0)
      (coe d852 v0)
name908 = "Algebra.CommutativeSemiring._.zero"
d908 v0 v1 v2 = du908 v2
du908 v0
  = coe MAlonzo.Code.Algebra.Structures.du1860 erased erased
      (coe d846 v0)
      (coe d848 v0)
      (coe d852 v0)
name910 = "Algebra.CommutativeSemiring._.zero\737"
d910 v0 = coe MAlonzo.Code.Algebra.Structures.d1772 (coe d852 v0)
name912 = "Algebra.CommutativeSemiring.semiring"
d912 v0 v1 v2 = du912 v2
du912 v0
  = coe C193 erased erased (coe d844 v0) (coe d846 v0) (coe d848 v0)
      (coe d850 v0)
      (coe du894 v0)
name916 = "Algebra.CommutativeSemiring._.*-monoid"
d916 v0 v1 v2 = du916 v2
du916 v0
  = coe C37 erased erased (coe d642 (coe du912 v0))
      (coe d646 (coe du912 v0))
      (coe MAlonzo.Code.Algebra.Structures.d1248
         (coe MAlonzo.Code.Algebra.Structures.d1416
            (coe d648 (coe du912 v0))))
name918 = "Algebra.CommutativeSemiring._.rawMonoid"
d918 v0 v1 v2 = du918 v2
du918 v0
  = coe C19 erased erased (coe d642 (coe du912 v0))
      (coe d646 (coe du912 v0))
name920 = "Algebra.CommutativeSemiring._.semigroup"
d920 v0 v1 v2 = du920 v2
du920 v0
  = coe C5 erased erased (coe d642 (coe du912 v0))
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d1248
            (coe MAlonzo.Code.Algebra.Structures.d1416
               (coe d648 (coe du912 v0)))))
name922 = "Algebra.CommutativeSemiring._.+-commutativeMonoid"
d922 v0 v1 v2 = du922 v2
du922 v0
  = coe C61 erased erased (coe d640 (coe du912 v0))
      (coe d644 (coe du912 v0))
      (coe MAlonzo.Code.Algebra.Structures.d1246
         (coe MAlonzo.Code.Algebra.Structures.d1416
            (coe d648 (coe du912 v0))))
name924 = "Algebra.CommutativeSemiring._.monoid"
d924 v0 v1 v2 = du924 v2
du924 v0 = coe du708 (coe du912 v0)
name926 = "Algebra.CommutativeSemiring._.rawMonoid"
d926 v0 v1 v2 = du926 v2
du926 v0 = coe du710 (coe du912 v0)
name928 = "Algebra.CommutativeSemiring._.semigroup"
d928 v0 v1 v2 = du928 v2
du928 v0 = coe du712 (coe du912 v0)
name930 = "Algebra.CommutativeSemiring._.nearSemiring"
d930 v0 v1 v2 = du930 v2
du930 v0 = coe du720 (coe du912 v0)
name932
  = "Algebra.CommutativeSemiring._.semiringWithoutAnnihilatingZero"
d932 v0 v1 v2 = du932 v2
du932 v0
  = coe C169 erased erased (coe d640 (coe du912 v0))
      (coe d642 (coe du912 v0))
      (coe d644 (coe du912 v0))
      (coe d646 (coe du912 v0))
      (coe MAlonzo.Code.Algebra.Structures.d1416
         (coe d648 (coe du912 v0)))
name934 = "Algebra.CommutativeSemiring._.semiringWithoutOne"
d934 v0 v1 v2 = du934 v2
du934 v0
  = coe C147 erased erased (coe d640 (coe du912 v0))
      (coe d642 (coe du912 v0))
      (coe d644 (coe du912 v0))
      (coe MAlonzo.Code.Algebra.Structures.C199
         (coe MAlonzo.Code.Algebra.Structures.d1246
            (coe MAlonzo.Code.Algebra.Structures.d1416
               (coe d648 (coe du912 v0))))
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d1248
               (coe MAlonzo.Code.Algebra.Structures.d1416
                  (coe d648 (coe du912 v0)))))
         (coe MAlonzo.Code.Algebra.Structures.d1250
            (coe MAlonzo.Code.Algebra.Structures.d1416
               (coe d648 (coe du912 v0))))
         (coe MAlonzo.Code.Algebra.Structures.d1418
            (coe d648 (coe du912 v0))))
name936 = "Algebra.CommutativeSemiring._.setoid"
d936 v0 v1 v2 = du936 v2
du936 v0 = coe du714 (coe du912 v0)
name938 = "Algebra.CommutativeSemiring.*-commutativeMonoid"
d938 v0
  = coe C61 erased erased (coe d846 v0) (coe d850 v0)
      (coe MAlonzo.Code.Algebra.Structures.d1768 (coe d852 v0))
name940
  = "Algebra.CommutativeSemiring.commutativeSemiringWithoutOne"
d940 v0 v1 v2 = du940 v2
du940 v0
  = coe C217 erased erased (coe d844 v0) (coe d846 v0) (coe d848 v0)
      (coe du888 v0)
name944 = "Algebra.RawRing"
d944 a0 = ()

data T944 a0 a1 a2 a3 a4 a5 = C259 a0 a1 a2 a3 a4 a5
name960 = "Algebra.RawRing.Carrier"
d960 = erased
name962 = "Algebra.RawRing._+_"
d962 v0
  = case coe v0 of
        C259 v1 v2 v3 v4 v5 v6 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name964 = "Algebra.RawRing._*_"
d964 v0
  = case coe v0 of
        C259 v1 v2 v3 v4 v5 v6 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name966 = "Algebra.RawRing.-_"
d966 v0
  = case coe v0 of
        C259 v1 v2 v3 v4 v5 v6 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name968 = "Algebra.RawRing.0#"
d968 v0
  = case coe v0 of
        C259 v1 v2 v3 v4 v5 v6 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name970 = "Algebra.RawRing.1#"
d970 v0
  = case coe v0 of
        C259 v1 v2 v3 v4 v5 v6 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name976 = "Algebra.Ring"
d976 a0 a1 = ()

data T976 a0 a1 a2 a3 a4 a5 a6 a7 = C281 a0 a1 a2 a3 a4 a5 a6 a7
name998 = "Algebra.Ring.Carrier"
d998 = erased
name1000 = "Algebra.Ring._\8776_"
d1000 = erased
name1002 = "Algebra.Ring._+_"
d1002 v0
  = case coe v0 of
        C281 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1004 = "Algebra.Ring._*_"
d1004 v0
  = case coe v0 of
        C281 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1006 = "Algebra.Ring.-_"
d1006 v0
  = case coe v0 of
        C281 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1008 = "Algebra.Ring.0#"
d1008 v0
  = case coe v0 of
        C281 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1010 = "Algebra.Ring.1#"
d1010 v0
  = case coe v0 of
        C281 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1012 = "Algebra.Ring.isRing"
d1012 v0
  = case coe v0 of
        C281 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1016 = "Algebra.Ring._._-_"
d1016 v0 v1 v2 = du1016 v2
du1016 v0
  = coe MAlonzo.Code.Algebra.Structures.du2058 (coe d1002 v0)
      (coe d1006 v0)
name1018 = "Algebra.Ring._.assoc"
d1018 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d2052 (coe d1012 v0)))
name1020 = "Algebra.Ring._.\8729-cong"
d1020 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d2052 (coe d1012 v0)))
name1022 = "Algebra.Ring._.identity"
d1022 v0
  = coe MAlonzo.Code.Algebra.Structures.d264
      (coe MAlonzo.Code.Algebra.Structures.d2052 (coe d1012 v0))
name1024 = "Algebra.Ring._.*-isMonoid"
d1024 v0 = coe MAlonzo.Code.Algebra.Structures.d2052 (coe d1012 v0)
name1026 = "Algebra.Ring._.isSemigroup"
d1026 v0
  = coe MAlonzo.Code.Algebra.Structures.d262
      (coe MAlonzo.Code.Algebra.Structures.d2052 (coe d1012 v0))
name1028 = "Algebra.Ring._.assoc"
d1028 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746
               (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)))))
name1030 = "Algebra.Ring._.comm"
d1030 v0
  = coe MAlonzo.Code.Algebra.Structures.d748
      (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))
name1032 = "Algebra.Ring._.\8729-cong"
d1032 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746
               (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)))))
name1034 = "Algebra.Ring._.identity"
d1034 v0
  = coe MAlonzo.Code.Algebra.Structures.d264
      (coe MAlonzo.Code.Algebra.Structures.d588
         (coe MAlonzo.Code.Algebra.Structures.d746
            (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))))
name1036 = "Algebra.Ring._.+-isAbelianGroup"
d1036 v0 = coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)
name1038 = "Algebra.Ring._.isCommutativeMonoid"
d1038 v0
  = coe MAlonzo.Code.Algebra.Structures.C71
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746
               (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)))))
      (coe MAlonzo.Code.Data.Product.d26
         (coe MAlonzo.Code.Algebra.Structures.d264
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))))))
      (coe MAlonzo.Code.Algebra.Structures.d748
         (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)))
name1040 = "Algebra.Ring._.isGroup"
d1040 v0
  = coe MAlonzo.Code.Algebra.Structures.d746
      (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))
name1042 = "Algebra.Ring._.isMonoid"
d1042 v0
  = coe MAlonzo.Code.Algebra.Structures.d588
      (coe MAlonzo.Code.Algebra.Structures.d746
         (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)))
name1044 = "Algebra.Ring._.isSemigroup"
d1044 v0
  = coe MAlonzo.Code.Algebra.Structures.d262
      (coe MAlonzo.Code.Algebra.Structures.d588
         (coe MAlonzo.Code.Algebra.Structures.d746
            (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))))
name1046 = "Algebra.Ring._.\8315\185-cong"
d1046 v0
  = coe MAlonzo.Code.Algebra.Structures.d592
      (coe MAlonzo.Code.Algebra.Structures.d746
         (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)))
name1048 = "Algebra.Ring._.inverse"
d1048 v0
  = coe MAlonzo.Code.Algebra.Structures.d590
      (coe MAlonzo.Code.Algebra.Structures.d746
         (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)))
name1050 = "Algebra.Ring._.distrib"
d1050 v0 = coe MAlonzo.Code.Algebra.Structures.d2054 (coe d1012 v0)
name1052 = "Algebra.Ring._.isEquivalence"
d1052 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746
               (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)))))
name1054 = "Algebra.Ring._.isNearSemiring"
d1054 v0 v1 v2 = du1054 v2
du1054 v0
  = coe MAlonzo.Code.Algebra.Structures.du2140 erased erased
      (coe d1002 v0)
      (coe d1004 v0)
      (coe d1006 v0)
      (coe d1008 v0)
      (coe d1012 v0)
name1056 = "Algebra.Ring._.isSemiring"
d1056 v0 v1 v2 = du1056 v2
du1056 v0
  = coe MAlonzo.Code.Algebra.Structures.du2136 erased erased
      (coe d1002 v0)
      (coe d1004 v0)
      (coe d1006 v0)
      (coe d1008 v0)
      (coe d1012 v0)
name1058 = "Algebra.Ring._.isSemiringWithoutAnnihilatingZero"
d1058 v0
  = coe MAlonzo.Code.Algebra.Structures.C237
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)))))
         (coe MAlonzo.Code.Data.Product.d26
            (coe MAlonzo.Code.Algebra.Structures.d264
               (coe MAlonzo.Code.Algebra.Structures.d588
                  (coe MAlonzo.Code.Algebra.Structures.d746
                     (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))))))
         (coe MAlonzo.Code.Algebra.Structures.d748
            (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))))
      (coe MAlonzo.Code.Algebra.Structures.d2052 (coe d1012 v0))
      (coe MAlonzo.Code.Algebra.Structures.d2054 (coe d1012 v0))
name1060 = "Algebra.Ring._.isSemiringWithoutOne"
d1060 v0 v1 v2 = du1060 v2
du1060 v0
  = coe MAlonzo.Code.Algebra.Structures.du2142 erased erased
      (coe d1002 v0)
      (coe d1004 v0)
      (coe d1006 v0)
      (coe d1008 v0)
      (coe d1012 v0)
name1062 = "Algebra.Ring._.refl"
d1062 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))))))
name1064 = "Algebra.Ring._.reflexive"
d1064 v0 v1 v2 = du1064 v2
du1064 v0
  = coe MAlonzo.Code.Algebra.Structures.du2084 (coe d1012 v0)
name1066 = "Algebra.Ring._.sym"
d1066 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))))))
name1068 = "Algebra.Ring._.trans"
d1068 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))))))
name1070 = "Algebra.Ring._.zero"
d1070 v0 v1 v2 = du1070 v2
du1070 v0
  = coe MAlonzo.Code.Algebra.Structures.du2100 erased erased
      (coe d1002 v0)
      (coe d1004 v0)
      (coe d1006 v0)
      (coe d1008 v0)
      (coe d1012 v0)
name1072 = "Algebra.Ring.+-abelianGroup"
d1072 v0
  = coe C103 erased erased (coe d1002 v0) (coe d1008 v0)
      (coe d1006 v0)
      (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0))
name1074 = "Algebra.Ring.semiring"
d1074 v0 v1 v2 = du1074 v2
du1074 v0
  = coe C193 erased erased (coe d1002 v0) (coe d1004 v0)
      (coe d1008 v0)
      (coe d1010 v0)
      (coe du1056 v0)
name1078 = "Algebra.Ring._.*-monoid"
d1078 v0 v1 v2 = du1078 v2
du1078 v0
  = coe C37 erased erased (coe d642 (coe du1074 v0))
      (coe d646 (coe du1074 v0))
      (coe MAlonzo.Code.Algebra.Structures.d1248
         (coe MAlonzo.Code.Algebra.Structures.d1416
            (coe d648 (coe du1074 v0))))
name1080 = "Algebra.Ring._.rawMonoid"
d1080 v0 v1 v2 = du1080 v2
du1080 v0
  = coe C19 erased erased (coe d642 (coe du1074 v0))
      (coe d646 (coe du1074 v0))
name1082 = "Algebra.Ring._.semigroup"
d1082 v0 v1 v2 = du1082 v2
du1082 v0
  = coe C5 erased erased (coe d642 (coe du1074 v0))
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d1248
            (coe MAlonzo.Code.Algebra.Structures.d1416
               (coe d648 (coe du1074 v0)))))
name1084 = "Algebra.Ring._.+-commutativeMonoid"
d1084 v0 v1 v2 = du1084 v2
du1084 v0
  = coe C61 erased erased (coe d640 (coe du1074 v0))
      (coe d644 (coe du1074 v0))
      (coe MAlonzo.Code.Algebra.Structures.d1246
         (coe MAlonzo.Code.Algebra.Structures.d1416
            (coe d648 (coe du1074 v0))))
name1086 = "Algebra.Ring._.monoid"
d1086 v0 v1 v2 = du1086 v2
du1086 v0 = coe du708 (coe du1074 v0)
name1088 = "Algebra.Ring._.rawMonoid"
d1088 v0 v1 v2 = du1088 v2
du1088 v0 = coe du710 (coe du1074 v0)
name1090 = "Algebra.Ring._.semigroup"
d1090 v0 v1 v2 = du1090 v2
du1090 v0 = coe du712 (coe du1074 v0)
name1092 = "Algebra.Ring._.nearSemiring"
d1092 v0 v1 v2 = du1092 v2
du1092 v0 = coe du720 (coe du1074 v0)
name1094 = "Algebra.Ring._.semiringWithoutAnnihilatingZero"
d1094 v0 v1 v2 = du1094 v2
du1094 v0
  = coe C169 erased erased (coe d640 (coe du1074 v0))
      (coe d642 (coe du1074 v0))
      (coe d644 (coe du1074 v0))
      (coe d646 (coe du1074 v0))
      (coe MAlonzo.Code.Algebra.Structures.d1416
         (coe d648 (coe du1074 v0)))
name1096 = "Algebra.Ring._.semiringWithoutOne"
d1096 v0 v1 v2 = du1096 v2
du1096 v0
  = coe C147 erased erased (coe d640 (coe du1074 v0))
      (coe d642 (coe du1074 v0))
      (coe d644 (coe du1074 v0))
      (coe MAlonzo.Code.Algebra.Structures.C199
         (coe MAlonzo.Code.Algebra.Structures.d1246
            (coe MAlonzo.Code.Algebra.Structures.d1416
               (coe d648 (coe du1074 v0))))
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d1248
               (coe MAlonzo.Code.Algebra.Structures.d1416
                  (coe d648 (coe du1074 v0)))))
         (coe MAlonzo.Code.Algebra.Structures.d1250
            (coe MAlonzo.Code.Algebra.Structures.d1416
               (coe d648 (coe du1074 v0))))
         (coe MAlonzo.Code.Algebra.Structures.d1418
            (coe d648 (coe du1074 v0))))
name1098 = "Algebra.Ring._.setoid"
d1098 v0 v1 v2 = du1098 v2
du1098 v0 = coe du714 (coe du1074 v0)
name1102 = "Algebra.Ring._.group"
d1102 v0
  = coe C81 erased erased (coe d1002 v0) (coe d1008 v0)
      (coe d1006 v0)
      (coe MAlonzo.Code.Algebra.Structures.d746
         (coe MAlonzo.Code.Algebra.Structures.d2050 (coe d1012 v0)))
name1104 = "Algebra.Ring.rawRing"
d1104 v0
  = coe C259 erased (coe d1002 v0) (coe d1004 v0) (coe d1006 v0)
      (coe d1008 v0)
      (coe d1010 v0)
name1110 = "Algebra.CommutativeRing"
d1110 a0 a1 = ()

data T1110 a0 a1 a2 a3 a4 a5 a6 a7 = C309 a0 a1 a2 a3 a4 a5 a6 a7
name1132 = "Algebra.CommutativeRing.Carrier"
d1132 = erased
name1134 = "Algebra.CommutativeRing._\8776_"
d1134 = erased
name1136 = "Algebra.CommutativeRing._+_"
d1136 v0
  = case coe v0 of
        C309 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1138 = "Algebra.CommutativeRing._*_"
d1138 v0
  = case coe v0 of
        C309 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1140 = "Algebra.CommutativeRing.-_"
d1140 v0
  = case coe v0 of
        C309 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1142 = "Algebra.CommutativeRing.0#"
d1142 v0
  = case coe v0 of
        C309 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1144 = "Algebra.CommutativeRing.1#"
d1144 v0
  = case coe v0 of
        C309 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1146 = "Algebra.CommutativeRing.isCommutativeRing"
d1146 v0
  = case coe v0 of
        C309 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1150 = "Algebra.CommutativeRing._._-_"
d1150 v0 v1 v2 = du1150 v2
du1150 v0
  = coe MAlonzo.Code.Algebra.Structures.du2284 (coe d1136 v0)
      (coe d1140 v0)
name1152 = "Algebra.CommutativeRing._.assoc"
d1152 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d2052
            (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))
name1154 = "Algebra.CommutativeRing._.*-comm"
d1154 v0 = coe MAlonzo.Code.Algebra.Structures.d2280 (coe d1146 v0)
name1156 = "Algebra.CommutativeRing._.\8729-cong"
d1156 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d2052
            (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))
name1158 = "Algebra.CommutativeRing._.identity"
d1158 v0
  = coe MAlonzo.Code.Algebra.Structures.d264
      (coe MAlonzo.Code.Algebra.Structures.d2052
         (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))
name1160 = "Algebra.CommutativeRing._.*-isCommutativeMonoid"
d1160 v0 v1 v2 = du1160 v2
du1160 v0
  = coe MAlonzo.Code.Algebra.Structures.du2344 erased erased
      (coe d1136 v0)
      (coe d1138 v0)
      (coe d1140 v0)
      (coe d1142 v0)
      (coe d1146 v0)
name1162 = "Algebra.CommutativeRing._.*-isMonoid"
d1162 v0
  = coe MAlonzo.Code.Algebra.Structures.d2052
      (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))
name1164 = "Algebra.CommutativeRing._.isSemigroup"
d1164 v0
  = coe MAlonzo.Code.Algebra.Structures.d262
      (coe MAlonzo.Code.Algebra.Structures.d2052
         (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))
name1166 = "Algebra.CommutativeRing._.assoc"
d1166 v0
  = coe MAlonzo.Code.Algebra.Structures.d126
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746
               (coe MAlonzo.Code.Algebra.Structures.d2050
                  (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))))
name1168 = "Algebra.CommutativeRing._.comm"
d1168 v0
  = coe MAlonzo.Code.Algebra.Structures.d748
      (coe MAlonzo.Code.Algebra.Structures.d2050
         (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))
name1170 = "Algebra.CommutativeRing._.\8729-cong"
d1170 v0
  = coe MAlonzo.Code.Algebra.Structures.d128
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746
               (coe MAlonzo.Code.Algebra.Structures.d2050
                  (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))))
name1172 = "Algebra.CommutativeRing._.identity"
d1172 v0
  = coe MAlonzo.Code.Algebra.Structures.d264
      (coe MAlonzo.Code.Algebra.Structures.d588
         (coe MAlonzo.Code.Algebra.Structures.d746
            (coe MAlonzo.Code.Algebra.Structures.d2050
               (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))))
name1174 = "Algebra.CommutativeRing._.+-isAbelianGroup"
d1174 v0
  = coe MAlonzo.Code.Algebra.Structures.d2050
      (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))
name1176 = "Algebra.CommutativeRing._.isCommutativeMonoid"
d1176 v0
  = coe MAlonzo.Code.Algebra.Structures.C71
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746
               (coe MAlonzo.Code.Algebra.Structures.d2050
                  (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))))
      (coe MAlonzo.Code.Data.Product.d26
         (coe MAlonzo.Code.Algebra.Structures.d264
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050
                     (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))))))
      (coe MAlonzo.Code.Algebra.Structures.d748
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))
name1178 = "Algebra.CommutativeRing._.isGroup"
d1178 v0
  = coe MAlonzo.Code.Algebra.Structures.d746
      (coe MAlonzo.Code.Algebra.Structures.d2050
         (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))
name1180 = "Algebra.CommutativeRing._.isMonoid"
d1180 v0
  = coe MAlonzo.Code.Algebra.Structures.d588
      (coe MAlonzo.Code.Algebra.Structures.d746
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))
name1182 = "Algebra.CommutativeRing._.isSemigroup"
d1182 v0
  = coe MAlonzo.Code.Algebra.Structures.d262
      (coe MAlonzo.Code.Algebra.Structures.d588
         (coe MAlonzo.Code.Algebra.Structures.d746
            (coe MAlonzo.Code.Algebra.Structures.d2050
               (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))))
name1184 = "Algebra.CommutativeRing._.\8315\185-cong"
d1184 v0
  = coe MAlonzo.Code.Algebra.Structures.d592
      (coe MAlonzo.Code.Algebra.Structures.d746
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))
name1186 = "Algebra.CommutativeRing._.inverse"
d1186 v0
  = coe MAlonzo.Code.Algebra.Structures.d590
      (coe MAlonzo.Code.Algebra.Structures.d746
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))
name1188 = "Algebra.CommutativeRing._.distrib"
d1188 v0
  = coe MAlonzo.Code.Algebra.Structures.d2054
      (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))
name1190 = "Algebra.CommutativeRing._.isCommutativeSemiring"
d1190 v0 v1 v2 = du1190 v2
du1190 v0
  = coe MAlonzo.Code.Algebra.Structures.du2340 erased erased
      (coe d1136 v0)
      (coe d1138 v0)
      (coe d1140 v0)
      (coe d1142 v0)
      (coe d1146 v0)
name1192
  = "Algebra.CommutativeRing._.isCommutativeSemiringWithoutOne"
d1192 v0 v1 v2 = du1192 v2
du1192 v0
  = coe MAlonzo.Code.Algebra.Structures.du2346 erased erased
      (coe d1136 v0)
      (coe d1138 v0)
      (coe d1140 v0)
      (coe d1142 v0)
      (coe d1144 v0)
      (coe d1146 v0)
name1194 = "Algebra.CommutativeRing._.isEquivalence"
d1194 v0
  = coe MAlonzo.Code.Algebra.Structures.d124
      (coe MAlonzo.Code.Algebra.Structures.d262
         (coe MAlonzo.Code.Algebra.Structures.d588
            (coe MAlonzo.Code.Algebra.Structures.d746
               (coe MAlonzo.Code.Algebra.Structures.d2050
                  (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))))
name1196 = "Algebra.CommutativeRing._.isNearSemiring"
d1196 v0 v1 v2 = du1196 v2
du1196 v0
  = coe MAlonzo.Code.Algebra.Structures.du2322 erased erased
      (coe d1136 v0)
      (coe d1138 v0)
      (coe d1140 v0)
      (coe d1142 v0)
      (coe d1146 v0)
name1198 = "Algebra.CommutativeRing._.isRing"
d1198 v0 = coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)
name1200 = "Algebra.CommutativeRing._.isSemiring"
d1200 v0 v1 v2 = du1200 v2
du1200 v0
  = coe MAlonzo.Code.Algebra.Structures.du2324 erased erased
      (coe d1136 v0)
      (coe d1138 v0)
      (coe d1140 v0)
      (coe d1142 v0)
      (coe d1146 v0)
name1202
  = "Algebra.CommutativeRing._.isSemiringWithoutAnnihilatingZero"
d1202 v0
  = coe MAlonzo.Code.Algebra.Structures.C237
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050
                     (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))))
         (coe MAlonzo.Code.Data.Product.d26
            (coe MAlonzo.Code.Algebra.Structures.d264
               (coe MAlonzo.Code.Algebra.Structures.d588
                  (coe MAlonzo.Code.Algebra.Structures.d746
                     (coe MAlonzo.Code.Algebra.Structures.d2050
                        (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))))))
         (coe MAlonzo.Code.Algebra.Structures.d748
            (coe MAlonzo.Code.Algebra.Structures.d2050
               (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))))
      (coe MAlonzo.Code.Algebra.Structures.d2052
         (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))
      (coe MAlonzo.Code.Algebra.Structures.d2054
         (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))
name1204 = "Algebra.CommutativeRing._.isSemiringWithoutOne"
d1204 v0 v1 v2 = du1204 v2
du1204 v0
  = coe MAlonzo.Code.Algebra.Structures.du2328 erased erased
      (coe d1136 v0)
      (coe d1138 v0)
      (coe d1140 v0)
      (coe d1142 v0)
      (coe d1146 v0)
name1206 = "Algebra.CommutativeRing._.refl"
d1206 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050
                     (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))))))
name1208 = "Algebra.CommutativeRing._.reflexive"
d1208 v0 v1 v2 = du1208 v2
du1208 v0
  = coe MAlonzo.Code.Algebra.Structures.du2332 (coe d1146 v0)
name1210 = "Algebra.CommutativeRing._.sym"
d1210 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050
                     (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))))))
name1212 = "Algebra.CommutativeRing._.trans"
d1212 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050
                     (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))))))
name1214 = "Algebra.CommutativeRing._.zero"
d1214 v0 v1 v2 = du1214 v2
du1214 v0
  = coe MAlonzo.Code.Algebra.Structures.du2338 erased erased
      (coe d1136 v0)
      (coe d1138 v0)
      (coe d1140 v0)
      (coe d1142 v0)
      (coe d1146 v0)
name1216 = "Algebra.CommutativeRing.ring"
d1216 v0
  = coe C281 erased erased (coe d1136 v0) (coe d1138 v0)
      (coe d1140 v0)
      (coe d1142 v0)
      (coe d1144 v0)
      (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))
name1218 = "Algebra.CommutativeRing.commutativeSemiring"
d1218 v0 v1 v2 = du1218 v2
du1218 v0
  = coe C239 erased erased (coe d1136 v0) (coe d1138 v0)
      (coe d1142 v0)
      (coe d1144 v0)
      (coe du1190 v0)
name1222 = "Algebra.CommutativeRing._.+-abelianGroup"
d1222 v0
  = coe C103 erased erased (coe d1136 v0) (coe d1142 v0)
      (coe d1140 v0)
      (coe MAlonzo.Code.Algebra.Structures.d2050
         (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0)))
name1224 = "Algebra.CommutativeRing._.group"
d1224 v0
  = coe C81 erased erased (coe d1136 v0) (coe d1142 v0)
      (coe d1140 v0)
      (coe MAlonzo.Code.Algebra.Structures.d746
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.Structures.d2278 (coe d1146 v0))))
name1226 = "Algebra.CommutativeRing._.rawRing"
d1226 v0
  = coe C259 erased (coe d1136 v0) (coe d1138 v0) (coe d1140 v0)
      (coe d1142 v0)
      (coe d1144 v0)
name1230 = "Algebra.CommutativeRing._.*-commutativeMonoid"
d1230 v0 v1 v2 = du1230 v2
du1230 v0
  = coe C61 erased erased (coe d846 (coe du1218 v0))
      (coe d850 (coe du1218 v0))
      (coe MAlonzo.Code.Algebra.Structures.d1768
         (coe d852 (coe du1218 v0)))
name1232 = "Algebra.CommutativeRing._.*-monoid"
d1232 v0 v1 v2 = du1232 v2
du1232 v0 = coe du916 (coe du1218 v0)
name1234 = "Algebra.CommutativeRing._.rawMonoid"
d1234 v0 v1 v2 = du1234 v2
du1234 v0 = coe du918 (coe du1218 v0)
name1236 = "Algebra.CommutativeRing._.semigroup"
d1236 v0 v1 v2 = du1236 v2
du1236 v0 = coe du920 (coe du1218 v0)
name1238 = "Algebra.CommutativeRing._.+-commutativeMonoid"
d1238 v0 v1 v2 = du1238 v2
du1238 v0 = coe du922 (coe du1218 v0)
name1240 = "Algebra.CommutativeRing._.monoid"
d1240 v0 v1 v2 = du1240 v2
du1240 v0 = coe du924 (coe du1218 v0)
name1242 = "Algebra.CommutativeRing._.rawMonoid"
d1242 v0 v1 v2 = du1242 v2
du1242 v0 = coe du926 (coe du1218 v0)
name1244 = "Algebra.CommutativeRing._.semigroup"
d1244 v0 v1 v2 = du1244 v2
du1244 v0 = coe du928 (coe du1218 v0)
name1246
  = "Algebra.CommutativeRing._.commutativeSemiringWithoutOne"
d1246 v0 v1 v2 = du1246 v2
du1246 v0 = coe du940 (coe du1218 v0)
name1248 = "Algebra.CommutativeRing._.nearSemiring"
d1248 v0 v1 v2 = du1248 v2
du1248 v0 = coe du930 (coe du1218 v0)
name1250 = "Algebra.CommutativeRing._.semiring"
d1250 v0 v1 v2 = du1250 v2
du1250 v0 = coe du912 (coe du1218 v0)
name1252
  = "Algebra.CommutativeRing._.semiringWithoutAnnihilatingZero"
d1252 v0 v1 v2 = du1252 v2
du1252 v0 = coe du932 (coe du1218 v0)
name1254 = "Algebra.CommutativeRing._.semiringWithoutOne"
d1254 v0 v1 v2 = du1254 v2
du1254 v0 = coe du934 (coe du1218 v0)
name1256 = "Algebra.CommutativeRing._.setoid"
d1256 v0 v1 v2 = du1256 v2
du1256 v0 = coe du936 (coe du1218 v0)
name1262 = "Algebra.Lattice"
d1262 a0 a1 = ()

data T1262 a0 a1 a2 a3 a4 = C335 a0 a1 a2 a3 a4
name1278 = "Algebra.Lattice.Carrier"
d1278 = erased
name1280 = "Algebra.Lattice._\8776_"
d1280 = erased
name1282 = "Algebra.Lattice._\8744_"
d1282 v0
  = case coe v0 of
        C335 v1 v2 v3 v4 v5 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1284 = "Algebra.Lattice._\8743_"
d1284 v0
  = case coe v0 of
        C335 v1 v2 v3 v4 v5 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1286 = "Algebra.Lattice.isLattice"
d1286 v0
  = case coe v0 of
        C335 v1 v2 v3 v4 v5 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1290 = "Algebra.Lattice._.absorptive"
d1290 v0 = coe MAlonzo.Code.Algebra.Structures.d2496 (coe d1286 v0)
name1292 = "Algebra.Lattice._.isEquivalence"
d1292 v0 = coe MAlonzo.Code.Algebra.Structures.d2482 (coe d1286 v0)
name1294 = "Algebra.Lattice._.refl"
d1294 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d2482 (coe d1286 v0))
name1296 = "Algebra.Lattice._.reflexive"
d1296 v0 v1 v2 = du1296 v2
du1296 v0
  = coe MAlonzo.Code.Algebra.Structures.du2502 (coe d1286 v0)
name1298 = "Algebra.Lattice._.sym"
d1298 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d2482 (coe d1286 v0))
name1300 = "Algebra.Lattice._.trans"
d1300 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d2482 (coe d1286 v0))
name1302 = "Algebra.Lattice._.\8743-assoc"
d1302 v0 = coe MAlonzo.Code.Algebra.Structures.d2492 (coe d1286 v0)
name1304 = "Algebra.Lattice._.\8743-comm"
d1304 v0 = coe MAlonzo.Code.Algebra.Structures.d2490 (coe d1286 v0)
name1306 = "Algebra.Lattice._.\8743-cong"
d1306 v0 = coe MAlonzo.Code.Algebra.Structures.d2494 (coe d1286 v0)
name1308 = "Algebra.Lattice._.\8744-assoc"
d1308 v0 = coe MAlonzo.Code.Algebra.Structures.d2486 (coe d1286 v0)
name1310 = "Algebra.Lattice._.\8744-comm"
d1310 v0 = coe MAlonzo.Code.Algebra.Structures.d2484 (coe d1286 v0)
name1312 = "Algebra.Lattice._.\8744-cong"
d1312 v0 = coe MAlonzo.Code.Algebra.Structures.d2488 (coe d1286 v0)
name1314 = "Algebra.Lattice.setoid"
d1314 v0
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Algebra.Structures.d2482 (coe d1286 v0))
name1320 = "Algebra.DistributiveLattice"
d1320 a0 a1 = ()

data T1320 a0 a1 a2 a3 a4 = C355 a0 a1 a2 a3 a4
name1336 = "Algebra.DistributiveLattice.Carrier"
d1336 = erased
name1338 = "Algebra.DistributiveLattice._\8776_"
d1338 = erased
name1340 = "Algebra.DistributiveLattice._\8744_"
d1340 v0
  = case coe v0 of
        C355 v1 v2 v3 v4 v5 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1342 = "Algebra.DistributiveLattice._\8743_"
d1342 v0
  = case coe v0 of
        C355 v1 v2 v3 v4 v5 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1344 = "Algebra.DistributiveLattice.isDistributiveLattice"
d1344 v0
  = case coe v0 of
        C355 v1 v2 v3 v4 v5 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1348 = "Algebra.DistributiveLattice._.absorptive"
d1348 v0
  = coe MAlonzo.Code.Algebra.Structures.d2496
      (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0))
name1350 = "Algebra.DistributiveLattice._.isEquivalence"
d1350 v0
  = coe MAlonzo.Code.Algebra.Structures.d2482
      (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0))
name1352 = "Algebra.DistributiveLattice._.isLattice"
d1352 v0 = coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0)
name1354 = "Algebra.DistributiveLattice._.refl"
d1354 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d2482
         (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0)))
name1356 = "Algebra.DistributiveLattice._.reflexive"
d1356 v0 v1 v2 = du1356 v2
du1356 v0
  = coe MAlonzo.Code.Algebra.Structures.du2642 (coe d1344 v0)
name1358 = "Algebra.DistributiveLattice._.sym"
d1358 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d2482
         (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0)))
name1360 = "Algebra.DistributiveLattice._.trans"
d1360 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d2482
         (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0)))
name1362 = "Algebra.DistributiveLattice._.\8743-assoc"
d1362 v0
  = coe MAlonzo.Code.Algebra.Structures.d2492
      (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0))
name1364 = "Algebra.DistributiveLattice._.\8743-comm"
d1364 v0
  = coe MAlonzo.Code.Algebra.Structures.d2490
      (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0))
name1366 = "Algebra.DistributiveLattice._.\8743-cong"
d1366 v0
  = coe MAlonzo.Code.Algebra.Structures.d2494
      (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0))
name1368 = "Algebra.DistributiveLattice._.\8744-assoc"
d1368 v0
  = coe MAlonzo.Code.Algebra.Structures.d2486
      (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0))
name1370 = "Algebra.DistributiveLattice._.\8744-comm"
d1370 v0
  = coe MAlonzo.Code.Algebra.Structures.d2484
      (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0))
name1372 = "Algebra.DistributiveLattice._.\8744-cong"
d1372 v0
  = coe MAlonzo.Code.Algebra.Structures.d2488
      (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0))
name1374 = "Algebra.DistributiveLattice._.\8744-\8743-distrib\691"
d1374 v0 = coe MAlonzo.Code.Algebra.Structures.d2632 (coe d1344 v0)
name1376 = "Algebra.DistributiveLattice.lattice"
d1376 v0
  = coe C335 erased erased (coe d1340 v0) (coe d1342 v0)
      (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0))
name1380 = "Algebra.DistributiveLattice._.setoid"
d1380 v0
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Algebra.Structures.d2482
         (coe MAlonzo.Code.Algebra.Structures.d2630 (coe d1344 v0)))
name1386 = "Algebra.BooleanAlgebra"
d1386 a0 a1 = ()

data T1386 a0 a1 a2 a3 a4 a5 a6 a7 = C375 a0 a1 a2 a3 a4 a5 a6 a7
name1408 = "Algebra.BooleanAlgebra.Carrier"
d1408 = erased
name1410 = "Algebra.BooleanAlgebra._\8776_"
d1410 = erased
name1412 = "Algebra.BooleanAlgebra._\8744_"
d1412 v0
  = case coe v0 of
        C375 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1414 = "Algebra.BooleanAlgebra._\8743_"
d1414 v0
  = case coe v0 of
        C375 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1416 = "Algebra.BooleanAlgebra.\172_"
d1416 v0
  = case coe v0 of
        C375 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1418 = "Algebra.BooleanAlgebra.\8868"
d1418 v0
  = case coe v0 of
        C375 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1420 = "Algebra.BooleanAlgebra.\8869"
d1420 v0
  = case coe v0 of
        C375 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1422 = "Algebra.BooleanAlgebra.isBooleanAlgebra"
d1422 v0
  = case coe v0 of
        C375 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
        _ -> coe MAlonzo.RTE.mazUnreachableError
name1426 = "Algebra.BooleanAlgebra._.absorptive"
d1426 v0
  = coe MAlonzo.Code.Algebra.Structures.d2496
      (coe MAlonzo.Code.Algebra.Structures.d2630
         (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0)))
name1428 = "Algebra.BooleanAlgebra._.isDistributiveLattice"
d1428 v0 = coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0)
name1430 = "Algebra.BooleanAlgebra._.isEquivalence"
d1430 v0
  = coe MAlonzo.Code.Algebra.Structures.d2482
      (coe MAlonzo.Code.Algebra.Structures.d2630
         (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0)))
name1432 = "Algebra.BooleanAlgebra._.isLattice"
d1432 v0
  = coe MAlonzo.Code.Algebra.Structures.d2630
      (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0))
name1434 = "Algebra.BooleanAlgebra._.refl"
d1434 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d516
      (coe MAlonzo.Code.Algebra.Structures.d2482
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0))))
name1436 = "Algebra.BooleanAlgebra._.reflexive"
d1436 v0 v1 v2 = du1436 v2
du1436 v0
  = coe MAlonzo.Code.Algebra.Structures.du2816 (coe d1422 v0)
name1438 = "Algebra.BooleanAlgebra._.sym"
d1438 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d2482
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0))))
name1440 = "Algebra.BooleanAlgebra._.trans"
d1440 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d520
      (coe MAlonzo.Code.Algebra.Structures.d2482
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0))))
name1442 = "Algebra.BooleanAlgebra._.\172-cong"
d1442 v0 = coe MAlonzo.Code.Algebra.Structures.d2804 (coe d1422 v0)
name1444 = "Algebra.BooleanAlgebra._.\8743-assoc"
d1444 v0
  = coe MAlonzo.Code.Algebra.Structures.d2492
      (coe MAlonzo.Code.Algebra.Structures.d2630
         (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0)))
name1446 = "Algebra.BooleanAlgebra._.\8743-comm"
d1446 v0
  = coe MAlonzo.Code.Algebra.Structures.d2490
      (coe MAlonzo.Code.Algebra.Structures.d2630
         (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0)))
name1448 = "Algebra.BooleanAlgebra._.\8743-complement\691"
d1448 v0 = coe MAlonzo.Code.Algebra.Structures.d2802 (coe d1422 v0)
name1450 = "Algebra.BooleanAlgebra._.\8743-cong"
d1450 v0
  = coe MAlonzo.Code.Algebra.Structures.d2494
      (coe MAlonzo.Code.Algebra.Structures.d2630
         (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0)))
name1452 = "Algebra.BooleanAlgebra._.\8744-assoc"
d1452 v0
  = coe MAlonzo.Code.Algebra.Structures.d2486
      (coe MAlonzo.Code.Algebra.Structures.d2630
         (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0)))
name1454 = "Algebra.BooleanAlgebra._.\8744-comm"
d1454 v0
  = coe MAlonzo.Code.Algebra.Structures.d2484
      (coe MAlonzo.Code.Algebra.Structures.d2630
         (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0)))
name1456 = "Algebra.BooleanAlgebra._.\8744-complement\691"
d1456 v0 = coe MAlonzo.Code.Algebra.Structures.d2800 (coe d1422 v0)
name1458 = "Algebra.BooleanAlgebra._.\8744-cong"
d1458 v0
  = coe MAlonzo.Code.Algebra.Structures.d2488
      (coe MAlonzo.Code.Algebra.Structures.d2630
         (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0)))
name1460 = "Algebra.BooleanAlgebra._.\8744-\8743-distrib\691"
d1460 v0
  = coe MAlonzo.Code.Algebra.Structures.d2632
      (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0))
name1462 = "Algebra.BooleanAlgebra.distributiveLattice"
d1462 v0
  = coe C355 erased erased (coe d1412 v0) (coe d1414 v0)
      (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0))
name1466 = "Algebra.BooleanAlgebra._.lattice"
d1466 v0
  = coe C335 erased erased (coe d1412 v0) (coe d1414 v0)
      (coe MAlonzo.Code.Algebra.Structures.d2630
         (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0)))
name1468 = "Algebra.BooleanAlgebra._.setoid"
d1468 v0
  = coe MAlonzo.Code.Relation.Binary.C85 erased erased
      (coe MAlonzo.Code.Algebra.Structures.d2482
         (coe MAlonzo.Code.Algebra.Structures.d2630
            (coe MAlonzo.Code.Algebra.Structures.d2798 (coe d1422 v0))))