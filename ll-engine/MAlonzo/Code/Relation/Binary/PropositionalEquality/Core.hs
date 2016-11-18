{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
       where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.Consequences.Core
import qualified MAlonzo.Code.Relation.Binary.Core
name12 = "Relation.Binary.PropositionalEquality.Core.sym"
d12 = erased
name18 = "Relation.Binary.PropositionalEquality.Core.trans"
d18 = erased
name28 = "Relation.Binary.PropositionalEquality.Core.subst"
d28 v0 v1 v2 v3 v4 v5 v6 v7 = du28 v7
du28 v0 = coe v0
name42 = "Relation.Binary.PropositionalEquality.Core.resp\8322"
d42 v0 v1 v2 v3 = du42 v3
du42 v0
  = coe MAlonzo.Code.Relation.Binary.Consequences.Core.du20 v0
      (coe d28 erased erased erased)
name50 = "Relation.Binary.PropositionalEquality.Core.isEquivalence"
d50 v0 v1 = du50
du50
  = coe MAlonzo.Code.Relation.Binary.Core.C605 erased erased erased