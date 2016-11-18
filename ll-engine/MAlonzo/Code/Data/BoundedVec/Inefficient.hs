{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.BoundedVec.Inefficient where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
name10 = "Data.BoundedVec.Inefficient.BoundedVec"
d10 a0 a1 a2 = ()

data T10 a0 a1 a2 = C18 a0
                  | C26 a0 a1 a2
name34 = "Data.BoundedVec.Inefficient.\8593"
d34 v0 v1 v2 v3 = du34 v1 v3
du34 v0 v1
  = case coe v1 of
        C18 v2 -> coe C18
                    (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                       v0)
        C26 v2 v3 v4 -> coe C26
                          (coe ((Prelude.+) :: Integer -> Integer -> Integer) (1 :: Integer)
                             v2)
                          v3
                          (coe du34 v2 v4)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name46 = "Data.BoundedVec.Inefficient.fromList"
d46 v0 v1 v2 = du46 v2
du46 v0
  = case coe v0 of
        [] -> coe C18 (coe MAlonzo.Code.Data.List.Base.du226 (coe []))
        (:) v1 v2 -> coe C26 (coe MAlonzo.Code.Data.List.Base.du226 v2) v1
                       (coe du46 v2)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name58 = "Data.BoundedVec.Inefficient.toList"
d58 v0 v1 v2 v3 = du58 v3
du58 v0
  = case coe v0 of
        C18 v1 -> coe []
        C26 v1 v2 v3 -> coe (:) v2 (coe du58 v3)
        _ -> coe MAlonzo.RTE.mazUnreachableError