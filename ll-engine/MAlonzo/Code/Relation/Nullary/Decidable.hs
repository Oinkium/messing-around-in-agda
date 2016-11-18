{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Nullary.Decidable where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Unit
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Equivalence
import qualified MAlonzo.Code.Function.Injection
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified MAlonzo.Code.Relation.Nullary
name10 = "Relation.Nullary.Decidable.\8970_\8971"
d10 v0 v1 v2 = du10 v2
du10 v0
  = case coe v0 of
        MAlonzo.Code.Relation.Nullary.C22 v1 -> coe True
        MAlonzo.Code.Relation.Nullary.C26 v1 -> coe False
        _ -> coe MAlonzo.RTE.mazUnreachableError
name16 = "Relation.Nullary.Decidable.True"
d16 = erased
name24 = "Relation.Nullary.Decidable.False"
d24 = erased
name34 = "Relation.Nullary.Decidable.toWitness"
d34 v0 v1 v2 v3 = du34 v2
du34 v0
  = case coe v0 of
        MAlonzo.Code.Relation.Nullary.C22 v1 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name44 = "Relation.Nullary.Decidable.fromWitness"
d44 v0 v1 v2 = du44 v2
du44 v0
  = case coe v0 of
        MAlonzo.Code.Relation.Nullary.C22 v1 -> coe
                                                  MAlonzo.Code.Function.d80
                                                  erased
                                                  erased
                                                  erased
                                                  erased
                                                  erased
        MAlonzo.Code.Relation.Nullary.C26 v1 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name56 = "Relation.Nullary.Decidable.toWitnessFalse"
d56 = erased
name66 = "Relation.Nullary.Decidable.fromWitnessFalse"
d66 v0 v1 v2 = du66 v2
du66 v0
  = case coe v0 of
        MAlonzo.Code.Relation.Nullary.C22 v1 -> coe
                                                  MAlonzo.Code.Function.d138
                                                  erased
                                                  erased
                                                  erased
                                                  erased
                                                  erased
                                                  erased
                                                  (coe MAlonzo.Code.Function.d158 erased erased
                                                     erased
                                                     erased)
                                                  v1
        MAlonzo.Code.Relation.Nullary.C26 v1 -> coe
                                                  MAlonzo.Code.Function.d80
                                                  erased
                                                  erased
                                                  erased
                                                  erased
                                                  erased
        _ -> coe MAlonzo.RTE.mazUnreachableError
name80 = "Relation.Nullary.Decidable.map"
d80 v0 v1 v2 v3 v4 v5 = du80 v4 v5
du80 v0 v1
  = case coe v1 of
        MAlonzo.Code.Relation.Nullary.C22 v2 -> coe
                                                  MAlonzo.Code.Relation.Nullary.C22
                                                  (coe MAlonzo.Code.Function.Equality.d38
                                                     (coe MAlonzo.Code.Function.Equivalence.d34 v0)
                                                     v2)
        MAlonzo.Code.Relation.Nullary.C26 v2 -> coe
                                                  MAlonzo.Code.Relation.Nullary.C26
                                                  (coe MAlonzo.Code.Function.d38 erased erased
                                                     erased
                                                     erased
                                                     erased
                                                     erased
                                                     (\ v3 -> v2)
                                                     (coe MAlonzo.Code.Function.Equality.d38
                                                        (coe MAlonzo.Code.Function.Equivalence.d36
                                                           v0)))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name98 = "Relation.Nullary.Decidable.map\8242"
d98 v0 v1 v2 v3 v4 v5 = du98 v2 v3 v4 v5
du98 v0 v1 v2 v3
  = coe d80 erased erased erased erased
      (coe MAlonzo.Code.Function.Equivalence.du56 v0 v1 v2 v3)
name122 = "Relation.Nullary.Decidable._._._\8776_"
d122 = erased
name128 = "Relation.Nullary.Decidable._.via-injection"
d128 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du128 v6 v7 v8 v9
du128 v0 v1 v2 v3
  = let v4
          = coe v1
              (coe MAlonzo.Code.Function.Equality.d38
                 (coe MAlonzo.Code.Function.Injection.d106 v0)
                 v2)
              (coe MAlonzo.Code.Function.Equality.d38
                 (coe MAlonzo.Code.Function.Injection.d106 v0)
                 v3)
      in
      case coe v4 of
          MAlonzo.Code.Relation.Nullary.C22 v5 -> coe
                                                    MAlonzo.Code.Relation.Nullary.C22
                                                    (coe MAlonzo.Code.Function.Injection.d108 v0 v2
                                                       v3
                                                       v5)
          MAlonzo.Code.Relation.Nullary.C26 v5 -> coe
                                                    MAlonzo.Code.Relation.Nullary.C26
                                                    (\ v6 ->
                                                       coe v5
                                                         (coe MAlonzo.Code.Function.Equality.d40
                                                            (coe
                                                               MAlonzo.Code.Function.Injection.d106
                                                               v0)
                                                            v2
                                                            v3
                                                            v6))
          _ -> coe MAlonzo.RTE.mazUnreachableError
name168 = "Relation.Nullary.Decidable.From-yes"
d168 = erased
name178 = "Relation.Nullary.Decidable.from-yes"
d178 v0
  = case coe v0 of
        MAlonzo.Code.Relation.Nullary.C22 v1 -> coe v1
        MAlonzo.Code.Relation.Nullary.C26 v1 -> coe MAlonzo.Code.Level.C20
                                                  erased
        _ -> coe MAlonzo.RTE.mazUnreachableError
name186 = "Relation.Nullary.Decidable.From-no"
d186 = erased
name196 = "Relation.Nullary.Decidable.from-no"
d196 v0
  = case coe v0 of
        MAlonzo.Code.Relation.Nullary.C22 v1 -> coe MAlonzo.Code.Level.C20
                                                  erased
        MAlonzo.Code.Relation.Nullary.C26 v1 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError