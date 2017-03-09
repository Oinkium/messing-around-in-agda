{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Induction.Nat where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Unit
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Induction
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified MAlonzo.Code.Relation.Unary
name6 = "Induction.Nat.Rec"
d6 = erased
name16 = "Induction.Nat.rec-builder"
d16 v0 v1 v2 v3 = du16 v2 v3
du16 v0 v1
  = case coe v1 of
        0 -> coe MAlonzo.Code.Level.C20 erased
        _ -> let v2
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v1
                       (1 :: Integer)
               in coe v0 v2 (coe du16 v0 v2)
name30 = "Induction.Nat.rec"
d30 v0 = du30
du30
  = coe MAlonzo.Code.Induction.d54 erased erased erased erased erased
      (coe d16 erased)
name34 = "Induction.Nat.CRec"
d34 = erased
name44 = "Induction.Nat.cRec-builder"
d44 v0 v1 v2 v3
  = case coe v3 of
        0 -> coe MAlonzo.Code.Level.C20 erased
        _ -> let v4
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v3
                       (1 :: Integer)
               in
               coe MAlonzo.Code.Data.Product.C30 (coe v2 v4 (coe d60 v0 v1 v2 v4))
                 (coe d60 v0 v1 v2 v4)
name60 = "Induction.Nat._.ih"
d60 v0 v1 v2 v3 = coe d44 v0 v1 v2 v3
name64 = "Induction.Nat.cRec"
d64 v0
  = coe MAlonzo.Code.Induction.d54 erased erased erased erased erased
      (coe d44 v0)
name68 = "Induction.Nat.<-Rec"
d68 = erased
name70 = "Induction.Nat.<-well-founded"
d70 = erased
name74 = "Induction.Nat.<-well-founded\8242"
d74 = erased
name94 = "Induction.Nat._._.wfRec"
d94 v0 = du94
du94 = MAlonzo.Code.Induction.WellFounded.du110
name96 = "Induction.Nat._._.wfRec-builder"
d96 v0 = du96
du96
  = coe MAlonzo.Code.Induction.WellFounded.d102 erased erased erased
      erased
      erased
      erased
name100 = "Induction.Nat.\8826-Rec"
d100 = erased
name102 = "Induction.Nat.\8826-well-founded"
d102 = erased
name112 = "Induction.Nat._._.wfRec"
d112 v0 = du112
du112 = MAlonzo.Code.Induction.WellFounded.du110
name114 = "Induction.Nat._._.wfRec-builder"
d114 v0 = du114
du114
  = coe MAlonzo.Code.Induction.WellFounded.d102 erased erased erased
      erased
      erased
      erased