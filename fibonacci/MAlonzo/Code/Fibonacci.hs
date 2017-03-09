{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Fibonacci where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Data.Nat
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.IO
name2 = "Fibonacci.fib-helper"
d2 v0 v1 v2
  = case coe v0 of
        0 -> coe v2
        1 -> coe v1
        _ -> coe d2
               (coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                  (1 :: Integer))
               (coe ((Prelude.+) :: Integer -> Integer -> Integer) v1 v2)
               v1
name18 = "Fibonacci.fib"
d18 v0 = coe d2 v0 (1 :: Integer) (0 :: Integer)
name22 = "Fibonacci.2\8319"
d22 v0
  = case coe v0 of
        0 -> 1 :: Integer
        _ -> let v1
                   = coe ((Prelude.-) :: Integer -> Integer -> Integer) v0
                       (1 :: Integer)
               in
               coe ((Prelude.+) :: Integer -> Integer -> Integer) (coe d30 v1)
                 (coe d30 v1)
name30 = "Fibonacci._.prev"
d30 v0 = coe d22 v0
main = d32
name32 = "Fibonacci.main"
d32
  = coe MAlonzo.Code.IO.d42 () erased
      (coe MAlonzo.Code.IO.d150
         (coe MAlonzo.Code.Data.Nat.Show.d22 (coe d22 (100 :: Integer))))