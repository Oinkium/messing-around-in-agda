{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Fin.Subset where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.Properties.BooleanAlgebra
import qualified
       MAlonzo.Code.Algebra.Properties.BooleanAlgebra.Expression
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.Properties
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Vec
import qualified MAlonzo.Code.Relation.Binary.Vec.Pointwise
import qualified MAlonzo.Code.Relation.Nullary
name6 = "Data.Fin.Subset.Subset"
d6 = erased
name10 = "Data.Fin.Subset._\8712_"
d10 = erased
name18 = "Data.Fin.Subset._\8713_"
d18 = erased
name26 = "Data.Fin.Subset._\8838_"
d26 = erased
name36 = "Data.Fin.Subset._\8840_"
d36 = erased
name42 = "Data.Fin.Subset.booleanAlgebra"
d42 v0
  = coe MAlonzo.Code.Algebra.Properties.BooleanAlgebra.du306
      (coe
         MAlonzo.Code.Algebra.Properties.BooleanAlgebra.Expression.du296
         MAlonzo.Code.Data.Bool.Properties.d372
         v0)
      erased
      (coe MAlonzo.Code.Relation.Binary.Vec.Pointwise.d402 erased erased
         erased)
name50 = "Data.Fin.Subset.BA._\8743_"
d50 v0 = coe MAlonzo.Code.Algebra.d1414 (coe d42 v0)
name52 = "Data.Fin.Subset.BA._\8744_"
d52 v0 = coe MAlonzo.Code.Algebra.d1412 (coe d42 v0)
name82 = "Data.Fin.Subset.BA.\172_"
d82 v0 = coe MAlonzo.Code.Algebra.d1416 (coe d42 v0)
name104 = "Data.Fin.Subset.BA.\8868"
d104 v0 = coe MAlonzo.Code.Algebra.d1418 (coe d42 v0)
name106 = "Data.Fin.Subset.BA.\8869"
d106 v0 = coe MAlonzo.Code.Algebra.d1420 (coe d42 v0)
name110 = "Data.Fin.Subset.\8261_\8262"
d110 v0 v1 = du110 v1
du110 v0
  = case coe v0 of
        MAlonzo.Code.Data.Fin.C8 v1 -> coe MAlonzo.Code.Data.Vec.C22 v1
                                         (coe True)
                                         (coe d106 v1)
        MAlonzo.Code.Data.Fin.C14 v1 v2 -> coe MAlonzo.Code.Data.Vec.C22 v1
                                             (coe False)
                                             (coe du110 v2)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name116 = "Data.Fin.Subset.\8899"
d116 v0
  = coe MAlonzo.Code.Data.List.Base.d144 erased erased erased erased
      (coe d52 v0)
      (coe d106 v0)
name120 = "Data.Fin.Subset.\8898"
d120 v0
  = coe MAlonzo.Code.Data.List.Base.d144 erased erased erased erased
      (coe d50 v0)
      (coe d104 v0)
name126 = "Data.Fin.Subset.Nonempty"
d126 = erased
name136 = "Data.Fin.Subset.Empty"
d136 = erased
name142 = "Data.Fin.Subset.Lift"
d142 = erased