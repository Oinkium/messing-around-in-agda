{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.String.Base where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Core
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.TrustMe
name6 = "Data.String.Base._++_"
d6 = MAlonzo.Code.Agda.Builtin.String.d12
name8 = "Data.String.Base.toList"
d8 = MAlonzo.Code.Agda.Builtin.String.d8
name10 = "Data.String.Base.fromList"
d10 = MAlonzo.Code.Agda.Builtin.String.d10
name14 = "Data.String.Base.toList\8728fromList"
d14 = erased
name20 = "Data.String.Base.fromList\8728toList"
d20 = erased
name24 = "Data.String.Base.unlines"
d24 v0
  = case coe v0 of
        [] -> coe Data.Text.pack ""
        (:) v1 v2 -> coe d6 v1
                       (coe d6 (coe Data.Text.pack "\n") (coe d24 v2))
        _ -> coe MAlonzo.RTE.mazUnreachableError
name30 = "Data.String.Base.show"
d30 = MAlonzo.Code.Agda.Builtin.String.d18