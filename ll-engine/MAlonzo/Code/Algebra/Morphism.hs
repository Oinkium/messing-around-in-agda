{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.Morphism where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Algebra.Properties.Group
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
name18 = "Algebra.Morphism.Definitions.Morphism"
d18 = erased
name20 = "Algebra.Morphism.Definitions.Homomorphic\8320"
d20 = erased
name28 = "Algebra.Morphism.Definitions.Homomorphic\8321"
d28 = erased
name38 = "Algebra.Morphism.Definitions.Homomorphic\8322"
d38 = erased
name62 = "Algebra.Morphism._-Ring\10230_"
d62 a0 a1 a2 a3 a4 a5 = ()

data T62 a0 a1 a2 a3 a4 = C41 a0 a1 a2 a3 a4
name78 = "Algebra.Morphism.F._*_"
d78 v0 v1 v2 v3 v4 v5 = du78 v4
du78 v0 = coe MAlonzo.Code.Algebra.d1004 v0
name80 = "Algebra.Morphism.F._+_"
d80 v0 v1 v2 v3 v4 v5 = du80 v4
du80 v0 = coe MAlonzo.Code.Algebra.d1002 v0
name84 = "Algebra.Morphism.F._\8776_"
d84 = erased
name140 = "Algebra.Morphism.F.1#"
d140 v0 v1 v2 v3 v4 v5 = du140 v4
du140 v0 = coe MAlonzo.Code.Algebra.d1010 v0
name142 = "Algebra.Morphism.F.Carrier"
d142 = erased
name286 = "Algebra.Morphism._.Homomorphic\8320"
d286 = erased
name290 = "Algebra.Morphism._.Homomorphic\8322"
d290 = erased
name292 = "Algebra.Morphism._.Morphism"
d292 = erased
name308 = "Algebra.Morphism._-Ring\10230_.F._+_"
d308 v0 v1 v2 v3 v4 v5 v6 = du308 v4
du308 v0 = coe MAlonzo.Code.Algebra.d1002 v0
name342 = "Algebra.Morphism._-Ring\10230_.F.identity"
d342 v0 v1 v2 v3 v4 v5 v6 = du342 v4
du342 v0
  = coe MAlonzo.Code.Algebra.Structures.d264
      (coe MAlonzo.Code.Algebra.Structures.d588
         (coe MAlonzo.Code.Algebra.Structures.d746
            (coe MAlonzo.Code.Algebra.Structures.d2050
               (coe MAlonzo.Code.Algebra.d1012 v0))))
name360 = "Algebra.Morphism._-Ring\10230_.F.-_"
d360 v0 v1 v2 v3 v4 v5 v6 = du360 v4
du360 v0 = coe MAlonzo.Code.Algebra.d1006 v0
name364 = "Algebra.Morphism._-Ring\10230_.F.inverse"
d364 v0 v1 v2 v3 v4 v5 v6 = du364 v4
du364 v0
  = coe MAlonzo.Code.Algebra.Structures.d590
      (coe MAlonzo.Code.Algebra.Structures.d746
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.d1012 v0)))
name366 = "Algebra.Morphism._-Ring\10230_.F.0#"
d366 v0 v1 v2 v3 v4 v5 v6 = du366 v4
du366 v0 = coe MAlonzo.Code.Algebra.d1008 v0
name370 = "Algebra.Morphism._-Ring\10230_.F.Carrier"
d370 = erased
name412 = "Algebra.Morphism._-Ring\10230_.T._+_"
d412 v0 v1 v2 v3 v4 v5 v6 = du412 v5
du412 v0 = coe MAlonzo.Code.Algebra.d1002 v0
name416 = "Algebra.Morphism._-Ring\10230_.T._\8776_"
d416 = erased
name444 = "Algebra.Morphism._-Ring\10230_.T.group"
d444 v0 v1 v2 v3 v4 v5 v6 = du444 v5
du444 v0
  = coe MAlonzo.Code.Algebra.C81 erased erased
      (coe MAlonzo.Code.Algebra.d1002 v0)
      (coe MAlonzo.Code.Algebra.d1008 v0)
      (coe MAlonzo.Code.Algebra.d1006 v0)
      (coe MAlonzo.Code.Algebra.Structures.d746
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.d1012 v0)))
name464 = "Algebra.Morphism._-Ring\10230_.T.-_"
d464 v0 v1 v2 v3 v4 v5 v6 = du464 v5
du464 v0 = coe MAlonzo.Code.Algebra.d1006 v0
name470 = "Algebra.Morphism._-Ring\10230_.T.0#"
d470 v0 v1 v2 v3 v4 v5 v6 = du470 v5
du470 v0 = coe MAlonzo.Code.Algebra.d1008 v0
name474 = "Algebra.Morphism._-Ring\10230_.T.Carrier"
d474 = erased
name504 = "Algebra.Morphism._-Ring\10230_.T.setoid"
d504 v0 v1 v2 v3 v4 v5 v6 = du504 v5
du504 v0 = coe MAlonzo.Code.Algebra.du1098 v0
name506 = "Algebra.Morphism._-Ring\10230_.T.sym"
d506 v0 v1 v2 v3 v4 v5 v6 = du506 v5
du506 v0
  = coe MAlonzo.Code.Relation.Binary.Core.d518
      (coe MAlonzo.Code.Algebra.Structures.d124
         (coe MAlonzo.Code.Algebra.Structures.d262
            (coe MAlonzo.Code.Algebra.Structures.d588
               (coe MAlonzo.Code.Algebra.Structures.d746
                  (coe MAlonzo.Code.Algebra.Structures.d2050
                     (coe MAlonzo.Code.Algebra.d1012 v0))))))
name514 = "Algebra.Morphism._-Ring\10230_._.Homomorphic\8320"
d514 = erased
name522 = "Algebra.Morphism._-Ring\10230_.\10214_\10215"
d522 v0
  = case coe v0 of
        C41 v1 v2 v3 v4 v5 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name524 = "Algebra.Morphism._-Ring\10230_.\10214\10215-cong"
d524 v0
  = case coe v0 of
        C41 v1 v2 v3 v4 v5 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name526 = "Algebra.Morphism._-Ring\10230_.+-homo"
d526 v0
  = case coe v0 of
        C41 v1 v2 v3 v4 v5 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name528 = "Algebra.Morphism._-Ring\10230_.*-homo"
d528 v0
  = case coe v0 of
        C41 v1 v2 v3 v4 v5 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name530 = "Algebra.Morphism._-Ring\10230_.1-homo"
d530 v0
  = case coe v0 of
        C41 v1 v2 v3 v4 v5 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name536 = "Algebra.Morphism._-Ring\10230_._._\8718"
d536 v0 v1 v2 v3 v4 v5 v6 = du536 v5
du536 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe du504 v0)
name538 = "Algebra.Morphism._-Ring\10230_._._\8764\10216_\10217_"
d538 v0 v1 v2 v3 v4 v5 v6 = du538 v5
du538 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40 (coe du504 v0)
name552 = "Algebra.Morphism._-Ring\10230_.0-homo"
d552 v0 v1 v2 v3 v4 v5 v6 = du552 v4 v5 v6
du552 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Properties.Group.du156 (coe du444 v1)
      (coe d522 v2 (coe du366 v0))
      (coe d522 v2 (coe du366 v0))
      (coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
         (coe du538 v1
            (coe du412 v1 (coe d522 v2 (coe du366 v0))
               (coe d522 v2 (coe du366 v0)))
            (coe d522 v2 (coe du80 v0 (coe du366 v0) (coe du366 v0)))
            (coe d522 v2 (coe du366 v0))
            (coe du506 v1
               (coe d522 v2 (coe du80 v0 (coe du366 v0) (coe du366 v0)))
               (coe MAlonzo.Code.Algebra.d1002 v1 (coe d522 v2 (coe du366 v0))
                  (coe d522 v2 (coe du366 v0)))
               (coe d526 v2 (coe du366 v0) (coe du366 v0)))
            (coe du538 v1
               (coe d522 v2 (coe du308 v0 (coe du366 v0) (coe du366 v0)))
               (coe d522 v2 (coe du366 v0))
               (coe d522 v2 (coe du366 v0))
               (coe d524 v2
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1008 v0)
                     (coe du366 v0))
                  (coe du366 v0)
                  (coe MAlonzo.Code.Data.Product.d26 (coe du342 v0) (coe du366 v0)))
               (coe du536 v1 (coe d522 v2 (coe du366 v0))))))
name554 = "Algebra.Morphism._-Ring\10230_.-\8255homo"
d554 v0 v1 v2 v3 v4 v5 v6 v7 = du554 v4 v5 v6 v7
du554 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Properties.Group.du188 (coe du444 v1)
      (coe d522 v2 (coe du360 v0 v3))
      (coe d522 v2 v3)
      (coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
         (coe du538 v1
            (coe du412 v1 (coe d522 v2 (coe du360 v0 v3)) (coe d522 v2 v3))
            (coe d522 v2 (coe du80 v0 (coe du360 v0 v3) v3))
            (coe du470 v1)
            (coe du506 v1 (coe d522 v2 (coe du80 v0 (coe du360 v0 v3) v3))
               (coe MAlonzo.Code.Algebra.d1002 v1 (coe d522 v2 (coe du360 v0 v3))
                  (coe d522 v2 v3))
               (coe d526 v2 (coe du360 v0 v3) v3))
            (coe du538 v1 (coe d522 v2 (coe du308 v0 (coe du360 v0 v3) v3))
               (coe d522 v2 (coe MAlonzo.Code.Algebra.d1008 v0))
               (coe du470 v1)
               (coe d524 v2
                  (coe MAlonzo.Code.Algebra.d1002 v0
                     (coe MAlonzo.Code.Algebra.d1006 v0 v3)
                     v3)
                  (coe MAlonzo.Code.Algebra.d1008 v0)
                  (coe MAlonzo.Code.Data.Product.d26 (coe du364 v0) v3))
               (coe du538 v1 (coe d522 v2 (coe du366 v0)) (coe du470 v1)
                  (coe du470 v1)
                  (coe du552 v0 v1 v2)
                  (coe du536 v1 (coe du470 v1))))))