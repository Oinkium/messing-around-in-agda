{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Unit.NonEta where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Level
name6 = "Data.Unit.NonEta.Unit"
d6 = ()

data T6 = C8
name12 = "Data.Unit.NonEta.Hidden"
d12 = erased
name28 = "Data.Unit.NonEta.hide"
d28 v0 v1 v2 v3 v4 v5 v6 = du28 v4 v5
du28 v0 v1 = coe v0 v1
name38 = "Data.Unit.NonEta.reveal"
d38 v0 v1 v2 = du38 v2
du38 v0 = coe v0 erased