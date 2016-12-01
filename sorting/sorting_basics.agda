module sorting_basics where

import Level using (zero)

open import Relation.Binary.Core

open import Data.Nat.Base

ℕOrder : Rel ℕ Level.zero
ℕOrder m n = m < n




