{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Induction.WellFounded where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Induction
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Unary
name12 = "Induction.WellFounded.WfRec"
d12 = erased
name32 = "Induction.WellFounded.Acc"
d32 a0 a1 a2 a3 a4 = ()

newtype T32 a0 = C46 a0
name54 = "Induction.WellFounded.Well-founded"
d54 = erased
name72 = "Induction.WellFounded.Some.wfRec-builder"
d72 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du72 v6 v9
du72 v0 v1
  = coe v0 v1
      (coe d72 erased erased erased erased erased erased v0 v1 erased)
name86 = "Induction.WellFounded.Some.wfRec"
d86 v0 v1 v2 v3 v4 = du86
du86
  = coe MAlonzo.Code.Induction.d114 erased erased erased erased
      erased
      erased
      erased
      (coe d72 erased erased erased erased erased)
name102 = "Induction.WellFounded.All.wfRec-builder"
d102 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du102 v7
du102 v0
  = coe d72 erased erased erased erased erased erased v0 erased
      erased
name110 = "Induction.WellFounded.All.wfRec"
d110 v0 v1 v2 v3 v4 v5 = du110
du110
  = coe MAlonzo.Code.Induction.d54 erased erased erased erased erased
      (coe d102 erased erased erased erased erased erased)
name132 = "Induction.WellFounded.Subrelation.accessible"
d132 = erased
name140 = "Induction.WellFounded.Subrelation.well-founded"
d140 = erased
name164 = "Induction.WellFounded.Inverse-image.accessible"
d164 = erased
name172 = "Induction.WellFounded.Inverse-image.well-founded"
d172 = erased
name188 = "Induction.WellFounded.Transitive-closure._<\8314_"
d188 a0 a1 a2 a3 a4 a5 = ()

data T188 a0 a1 a2 a3 a4 = C196 a0 a1 a2
                         | C208 a0 a1 a2 a3 a4
name214
  = "Induction.WellFounded.Transitive-closure.downwards-closed"
d214 = erased
name226 = "Induction.WellFounded.Transitive-closure.accessible"
d226 = erased
name230
  = "Induction.WellFounded.Transitive-closure.accessible\8242"
d230 = erased
name248 = "Induction.WellFounded.Transitive-closure.well-founded"
d248 = erased
name274 = "Induction.WellFounded.Lexicographic._<_"
d274 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()

data T274 a0 a1 a2 a3 a4 = C286 a0 a1 a2 a3 a4
                         | C296 a0 a1 a2 a3
name304 = "Induction.WellFounded.Lexicographic.accessible"
d304 = erased
name312 = "Induction.WellFounded.Lexicographic.accessible\8242"
d312 = erased
name334 = "Induction.WellFounded.Lexicographic.well-founded"
d334 = erased