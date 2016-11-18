{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Category.Functor where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
name8 = "Category.Functor.RawFunctor"
d8 a0 a1 = ()

newtype T8 a0 = C1 a0
name24 = "Category.Functor.RawFunctor._<$>_"
d24 v0
  = case coe v0 of
        C1 v1 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name30 = "Category.Functor.RawFunctor._<$_"
d30 v0 v1 v2 v3 v4 v5 v6 = du30 v2 v3 v4 v5 v6
du30 v0 v1 v2 v3 v4
  = coe d24 v0 v2 v1
      (coe MAlonzo.Code.Function.d80 erased erased erased erased v3)
      v4