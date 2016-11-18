{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Char where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.On
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.TrustMe
import qualified MAlonzo.Code.Relation.Nullary
import qualified MAlonzo.Code.Relation.Nullary.Decidable
name4 = "Data.Char._\8799_"
d4 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Char.d32 v0 v1 in
      case coe v2 of
          False -> coe MAlonzo.Code.Relation.Nullary.C26 erased
          True -> coe MAlonzo.Code.Relation.Nullary.C22 erased
          _ -> coe MAlonzo.RTE.mazUnreachableError
name26 = "Data.Char._.whatever"
d26
  = error
      "MAlonzo Runtime Error: postulate evaluated: Data.Char._.whatever"
name28 = "Data.Char._==_"
d28 v0 v1
  = coe MAlonzo.Code.Relation.Nullary.Decidable.du10 (coe d4 v0 v1)
name42 = "Data.Char.setoid"
d42
  = coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du112
      erased
name44 = "Data.Char.decSetoid"
d44
  = coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du120
      erased
      d4
name46 = "Data.Char.strictTotalOrder"
d46
  = coe MAlonzo.Code.Relation.Binary.On.du718 erased
      MAlonzo.Code.Data.Nat.Properties.d684
      MAlonzo.Code.Data.Char.Base.d8