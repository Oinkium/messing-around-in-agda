{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.List where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Category.Monad
import qualified MAlonzo.Code.Category.Monad.Indexed
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
name6 = "Data.List.monoid"
d6 v0 v1 = du6
du6
  = coe MAlonzo.Code.Algebra.C37 erased erased
      (coe MAlonzo.Code.Data.List.Base.d18 erased erased)
      (coe [])
      (coe MAlonzo.Code.Algebra.Structures.C49
         (coe MAlonzo.Code.Algebra.Structures.C25
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
            erased
            erased)
         (coe MAlonzo.Code.Data.Product.C30 erased erased))
name60 = "Data.List._.identity"
d60 = erased
name66 = "Data.List._.assoc"
d66 = erased
name84 = "Data.List.monad"
d84 v0 = du84
du84
  = coe MAlonzo.Code.Category.Monad.Indexed.C1
      (\ v0 v1 v2 -> coe (:) v2 (coe []))
      (\ v0 v1 v2 v3 v4 v5 v6 ->
         coe MAlonzo.Code.Data.List.Base.du184
           (coe MAlonzo.Code.Data.List.Base.du56 v6 v5))
name94 = "Data.List.monadZero"
d94 v0 = du94
du94
  = coe MAlonzo.Code.Category.Monad.Indexed.C183 du84
      (\ v0 v1 v2 -> coe [])
name98 = "Data.List.monadPlus"
d98 v0 = du98
du98
  = coe MAlonzo.Code.Category.Monad.Indexed.C197 du94
      (\ v0 v1 -> coe MAlonzo.Code.Data.List.Base.d18 erased)
name112 = "Data.List.Monadic._._<$>_"
d112 v0 v1 v2 = du112 v2
du112 v0 = coe MAlonzo.Code.Category.Monad.du46 v0
name128 = "Data.List.Monadic._._\8859_"
d128 v0 v1 v2 = du128 v2
du128 v0 = coe MAlonzo.Code.Category.Monad.du62 v0
name146 = "Data.List.Monadic.sequence"
d146 v0 v1 v2 v3 v4 = du146 v2 v3 v4
du146 v0 v1 v2
  = case coe v2 of
        [] -> coe MAlonzo.Code.Category.Monad.Indexed.d46 v0 erased erased
                (coe [])
        (:) v3 v4 -> coe du128 v0 erased erased erased erased erased
                       (coe du112 v0 erased erased v1 () (coe (:)) v3)
                       (coe du146 v0 v1 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name158 = "Data.List.Monadic.mapM"
d158 v0 v1 v2 v3 v4 v5 v6 = du158 v2 v5 v6
du158 v0 v1 v2
  = coe MAlonzo.Code.Function.d38 erased erased erased erased erased
      erased
      (\ v3 -> coe d146 erased erased v0 v1)
      (coe MAlonzo.Code.Data.List.Base.d56 erased erased erased erased
         v2)