{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing where
import MAlonzo.RTE (coe, erased)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Algebra.Morphism
import qualified MAlonzo.Code.Algebra.Properties.AbelianGroup
import qualified MAlonzo.Code.Algebra.Properties.Ring
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
name24
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing"
d24 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()

data T24 a0 a1 a2 a3 = C15 a0 a1 a2 a3
name60
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing.isCommutativeSemiring"
d60 v0
  = case coe v0 of
        C15 v1 v2 v3 v4 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name62
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing.-\8255cong"
d62 v0
  = case coe v0 of
        C15 v1 v2 v3 v4 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name68
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing.-\8255*-distrib\737"
d68 v0
  = case coe v0 of
        C15 v1 v2 v3 v4 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name74
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing.-\8255+-comm"
d74 v0
  = case coe v0 of
        C15 v1 v2 v3 v4 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name78
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.assoc"
d78 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du78 v2 v3 v4 v5 v7 v8 v9
du78 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1874 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name80
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.comm"
d80 v0
  = coe MAlonzo.Code.Algebra.Structures.d410
      (coe MAlonzo.Code.Algebra.Structures.d1768 (coe d60 v0))
name82
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.\8729-cong"
d82 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du82 v2 v3 v4 v5 v7 v8 v9
du82 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1876 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name84
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.identity"
d84 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du84 v2 v3 v4 v5 v7 v8 v9
du84 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1878 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name86
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-isCommutativeMonoid"
d86 v0 = coe MAlonzo.Code.Algebra.Structures.d1768 (coe d60 v0)
name88
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.*-isMonoid"
d88 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du88 v2 v3 v4 v5 v7 v8 v9
du88 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1880 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name90
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.isSemigroup"
d90 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du90 v2 v3 v4 v5 v7 v8 v9
du90 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1882 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name92
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.assoc"
d92 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du92 v2 v3 v4 v5 v7 v8 v9
du92 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1884 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name94
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.comm"
d94 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du94 v2 v3 v4 v5 v7 v8 v9
du94 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1886 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name96
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.\8729-cong"
d96 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du96 v2 v3 v4 v5 v7 v8 v9
du96 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1888 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name98
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.identity"
d98 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du98 v2 v3 v4 v5 v7 v8 v9
du98 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1890 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name100
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.+-isCommutativeMonoid"
d100 v0 = coe MAlonzo.Code.Algebra.Structures.d1766 (coe d60 v0)
name102
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.isMonoid"
d102 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du102 v2 v3 v4 v5 v7 v8 v9
du102 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1892 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name104
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.isSemigroup"
d104 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du104 v2 v3 v4 v5 v7 v8 v9
du104 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1894 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name106
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.distrib"
d106 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du106 v2 v3 v4 v5 v9
du106 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du1846 v0 v1 v2 v3
      (coe d60 v4)
name108
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.distrib\691"
d108 v0 = coe MAlonzo.Code.Algebra.Structures.d1770 (coe d60 v0)
name110
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.isCommutativeSemiringWithoutOne"
d110 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du110 v2 v3 v4 v5 v7 v8 v9
du110 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1912 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name112
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.isEquivalence"
d112 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du112 v2 v3 v4 v5 v7 v8 v9
du112 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1896 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name114
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.isNearSemiring"
d114 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du114 v2 v3 v4 v5 v7 v8 v9
du114 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1898 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name116
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.isSemiring"
d116 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du116 v2 v3 v4 v5 v7 v8 v9
du116 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1870 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name118
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.isSemiringWithoutAnnihilatingZero"
d118 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du118 v2 v3 v4 v5 v7 v8 v9
du118 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1900 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name120
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.isSemiringWithoutOne"
d120 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du120 v2 v3 v4 v5 v7 v8 v9
du120 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1902 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name122
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.refl"
d122 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du122 v2 v3 v4 v5 v7 v8 v9
du122 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1904 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name124
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.reflexive"
d124 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du124 v2 v3 v4 v5 v7 v8 v9
du124 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1906 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name126
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.sym"
d126 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du126 v2 v3 v4 v5 v7 v8 v9
du126 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1908 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name128
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.trans"
d128 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du128 v2 v3 v4 v5 v7 v8 v9
du128 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Algebra.Structures.du1910 v0 v1 v2 v3 v4 v5
      (coe d60 v6)
name130
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.zero"
d130 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du130 v2 v3 v5 v7 v9
du130 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du1860 v0 v1 v2 v3
      (coe d60 v4)
name132
  = "Algebra.RingSolver.AlmostCommutativeRing.IsAlmostCommutativeRing._.zero\737"
d132 v0 = coe MAlonzo.Code.Algebra.Structures.d1772 (coe d60 v0)
name138
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing"
d138 a0 a1 = ()

data T138 a0 a1 a2 a3 a4 a5 a6 a7 = C33 a0 a1 a2 a3 a4 a5 a6 a7
name160
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing.Carrier"
d160 = erased
name162
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._\8776_"
d162 = erased
name164
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._+_"
d164 v0
  = case coe v0 of
        C33 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name166
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._*_"
d166 v0
  = case coe v0 of
        C33 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name168
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing.-_"
d168 v0
  = case coe v0 of
        C33 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name170
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing.0#"
d170 v0
  = case coe v0 of
        C33 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name172
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing.1#"
d172 v0
  = case coe v0 of
        C33 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
        _ -> coe MAlonzo.RTE.mazUnreachableError
name174
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing.isAlmostCommutativeRing"
d174 v0
  = case coe v0 of
        C33 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
        _ -> coe MAlonzo.RTE.mazUnreachableError
name178
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.assoc"
d178 v0 v1 v2 = du178 v2
du178 v0
  = coe du78 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name180
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.comm"
d180 v0
  = coe MAlonzo.Code.Algebra.Structures.d410
      (coe MAlonzo.Code.Algebra.Structures.d1768 (coe d60 (coe d174 v0)))
name182
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.\8729-cong"
d182 v0 v1 v2 = du182 v2
du182 v0
  = coe du82 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name184
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.identity"
d184 v0 v1 v2 = du184 v2
du184 v0
  = coe du84 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name186
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.*-isCommutativeMonoid"
d186 v0
  = coe MAlonzo.Code.Algebra.Structures.d1768 (coe d60 (coe d174 v0))
name188
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.*-isMonoid"
d188 v0 v1 v2 = du188 v2
du188 v0
  = coe du88 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name190
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.isSemigroup"
d190 v0 v1 v2 = du190 v2
du190 v0
  = coe du90 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name192
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.assoc"
d192 v0 v1 v2 = du192 v2
du192 v0
  = coe du92 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name194
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.comm"
d194 v0 v1 v2 = du194 v2
du194 v0
  = coe du94 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name196
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.\8729-cong"
d196 v0 v1 v2 = du196 v2
du196 v0
  = coe du96 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name198
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.identity"
d198 v0 v1 v2 = du198 v2
du198 v0
  = coe du98 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name200
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.+-isCommutativeMonoid"
d200 v0
  = coe MAlonzo.Code.Algebra.Structures.d1766 (coe d60 (coe d174 v0))
name202
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.isMonoid"
d202 v0 v1 v2 = du202 v2
du202 v0
  = coe du102 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name204
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.isSemigroup"
d204 v0 v1 v2 = du204 v2
du204 v0
  = coe du104 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name206
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.-\8255*-distrib\737"
d206 v0 = coe d68 (coe d174 v0)
name208
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.-\8255+-comm"
d208 v0 = coe d74 (coe d174 v0)
name210
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.-\8255cong"
d210 v0 = coe d62 (coe d174 v0)
name212
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.distrib"
d212 v0 v1 v2 = du212 v2
du212 v0
  = coe du106 erased erased (coe d164 v0) (coe d166 v0) (coe d174 v0)
name214
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.distrib\691"
d214 v0
  = coe MAlonzo.Code.Algebra.Structures.d1770 (coe d60 (coe d174 v0))
name216
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.isCommutativeSemiring"
d216 v0 = coe d60 (coe d174 v0)
name218
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.isCommutativeSemiringWithoutOne"
d218 v0 v1 v2 = du218 v2
du218 v0
  = coe du110 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name220
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.isEquivalence"
d220 v0 v1 v2 = du220 v2
du220 v0
  = coe du112 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name222
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.isNearSemiring"
d222 v0 v1 v2 = du222 v2
du222 v0
  = coe du114 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name224
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.isSemiring"
d224 v0 v1 v2 = du224 v2
du224 v0
  = coe du116 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name226
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.isSemiringWithoutAnnihilatingZero"
d226 v0 v1 v2 = du226 v2
du226 v0
  = coe du118 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name228
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.isSemiringWithoutOne"
d228 v0 v1 v2 = du228 v2
du228 v0
  = coe du120 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name230
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.refl"
d230 v0 v1 v2 = du230 v2
du230 v0
  = coe du122 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name232
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.reflexive"
d232 v0 v1 v2 = du232 v2
du232 v0
  = coe du124 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name234
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.sym"
d234 v0 v1 v2 = du234 v2
du234 v0
  = coe du126 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name236
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.trans"
d236 v0 v1 v2 = du236 v2
du236 v0
  = coe du128 erased erased (coe d164 v0) (coe d166 v0) (coe d170 v0)
      (coe d172 v0)
      (coe d174 v0)
name238
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.zero"
d238 v0 v1 v2 = du238 v2
du238 v0
  = coe du130 erased erased (coe d166 v0) (coe d170 v0) (coe d174 v0)
name240
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.zero\737"
d240 v0
  = coe MAlonzo.Code.Algebra.Structures.d1772 (coe d60 (coe d174 v0))
name242
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing.commutativeSemiring"
d242 v0
  = coe MAlonzo.Code.Algebra.C239 erased erased (coe d164 v0)
      (coe d166 v0)
      (coe d170 v0)
      (coe d172 v0)
      (coe d60 (coe d174 v0))
name246
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.*-commutativeMonoid"
d246 v0
  = coe MAlonzo.Code.Algebra.C61 erased erased (coe d166 v0)
      (coe d172 v0)
      (coe MAlonzo.Code.Algebra.Structures.d1768 (coe d60 (coe d174 v0)))
name248
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.*-monoid"
d248 v0 v1 v2 = du248 v2
du248 v0
  = coe MAlonzo.Code.Algebra.du916
      (coe MAlonzo.Code.Algebra.C239 erased erased (coe d164 v0)
         (coe d166 v0)
         (coe d170 v0)
         (coe d172 v0)
         (coe d60 (coe d174 v0)))
name250
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.semigroup"
d250 v0 v1 v2 = du250 v2
du250 v0
  = coe MAlonzo.Code.Algebra.du920
      (coe MAlonzo.Code.Algebra.C239 erased erased (coe d164 v0)
         (coe d166 v0)
         (coe d170 v0)
         (coe d172 v0)
         (coe d60 (coe d174 v0)))
name252
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.+-commutativeMonoid"
d252 v0 v1 v2 = du252 v2
du252 v0
  = coe MAlonzo.Code.Algebra.du922
      (coe MAlonzo.Code.Algebra.C239 erased erased (coe d164 v0)
         (coe d166 v0)
         (coe d170 v0)
         (coe d172 v0)
         (coe d60 (coe d174 v0)))
name254
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.monoid"
d254 v0 v1 v2 = du254 v2
du254 v0
  = coe MAlonzo.Code.Algebra.du924
      (coe MAlonzo.Code.Algebra.C239 erased erased (coe d164 v0)
         (coe d166 v0)
         (coe d170 v0)
         (coe d172 v0)
         (coe d60 (coe d174 v0)))
name256
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.semigroup"
d256 v0 v1 v2 = du256 v2
du256 v0
  = coe MAlonzo.Code.Algebra.du928
      (coe MAlonzo.Code.Algebra.C239 erased erased (coe d164 v0)
         (coe d166 v0)
         (coe d170 v0)
         (coe d172 v0)
         (coe d60 (coe d174 v0)))
name258
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.semiring"
d258 v0 v1 v2 = du258 v2
du258 v0
  = coe MAlonzo.Code.Algebra.du912
      (coe MAlonzo.Code.Algebra.C239 erased erased (coe d164 v0)
         (coe d166 v0)
         (coe d170 v0)
         (coe d172 v0)
         (coe d60 (coe d174 v0)))
name260
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing._.setoid"
d260 v0 v1 v2 = du260 v2
du260 v0
  = coe MAlonzo.Code.Algebra.du936
      (coe MAlonzo.Code.Algebra.C239 erased erased (coe d164 v0)
         (coe d166 v0)
         (coe d170 v0)
         (coe d172 v0)
         (coe d60 (coe d174 v0)))
name262
  = "Algebra.RingSolver.AlmostCommutativeRing.AlmostCommutativeRing.rawRing"
d262 v0
  = coe MAlonzo.Code.Algebra.C259 erased (coe d164 v0) (coe d166 v0)
      (coe d168 v0)
      (coe d170 v0)
      (coe d172 v0)
name274
  = "Algebra.RingSolver.AlmostCommutativeRing._-Raw-AlmostCommutative\10230_"
d274 a0 a1 a2 a3 a4 = ()

data T274 a0 a1 a2 a3 a4 a5 = C71 a0 a1 a2 a3 a4 a5
name288 = "Algebra.RingSolver.AlmostCommutativeRing.F._*_"
d288 v0 v1 v2 v3 v4 = du288 v3
du288 v0 = coe MAlonzo.Code.Algebra.d964 v0
name290 = "Algebra.RingSolver.AlmostCommutativeRing.F._+_"
d290 v0 v1 v2 v3 v4 = du290 v3
du290 v0 = coe MAlonzo.Code.Algebra.d962 v0
name292 = "Algebra.RingSolver.AlmostCommutativeRing.F.-_"
d292 v0 v1 v2 v3 v4 = du292 v3
du292 v0 = coe MAlonzo.Code.Algebra.d966 v0
name294 = "Algebra.RingSolver.AlmostCommutativeRing.F.0#"
d294 v0 v1 v2 v3 v4 = du294 v3
du294 v0 = coe MAlonzo.Code.Algebra.d968 v0
name296 = "Algebra.RingSolver.AlmostCommutativeRing.F.1#"
d296 v0 v1 v2 v3 v4 = du296 v3
du296 v0 = coe MAlonzo.Code.Algebra.d970 v0
name298 = "Algebra.RingSolver.AlmostCommutativeRing.F.Carrier"
d298 = erased
name404
  = "Algebra.RingSolver.AlmostCommutativeRing._.Homomorphic\8320"
d404 = erased
name406
  = "Algebra.RingSolver.AlmostCommutativeRing._.Homomorphic\8321"
d406 = erased
name408
  = "Algebra.RingSolver.AlmostCommutativeRing._.Homomorphic\8322"
d408 = erased
name410 = "Algebra.RingSolver.AlmostCommutativeRing._.Morphism"
d410 = erased
name550
  = "Algebra.RingSolver.AlmostCommutativeRing._-Raw-AlmostCommutative\10230_.\10214_\10215"
d550 v0
  = case coe v0 of
        C71 v1 v2 v3 v4 v5 v6 -> coe v1
        _ -> coe MAlonzo.RTE.mazUnreachableError
name552
  = "Algebra.RingSolver.AlmostCommutativeRing._-Raw-AlmostCommutative\10230_.+-homo"
d552 v0
  = case coe v0 of
        C71 v1 v2 v3 v4 v5 v6 -> coe v2
        _ -> coe MAlonzo.RTE.mazUnreachableError
name554
  = "Algebra.RingSolver.AlmostCommutativeRing._-Raw-AlmostCommutative\10230_.*-homo"
d554 v0
  = case coe v0 of
        C71 v1 v2 v3 v4 v5 v6 -> coe v3
        _ -> coe MAlonzo.RTE.mazUnreachableError
name556
  = "Algebra.RingSolver.AlmostCommutativeRing._-Raw-AlmostCommutative\10230_.-\8255homo"
d556 v0
  = case coe v0 of
        C71 v1 v2 v3 v4 v5 v6 -> coe v4
        _ -> coe MAlonzo.RTE.mazUnreachableError
name558
  = "Algebra.RingSolver.AlmostCommutativeRing._-Raw-AlmostCommutative\10230_.0-homo"
d558 v0
  = case coe v0 of
        C71 v1 v2 v3 v4 v5 v6 -> coe v5
        _ -> coe MAlonzo.RTE.mazUnreachableError
name560
  = "Algebra.RingSolver.AlmostCommutativeRing._-Raw-AlmostCommutative\10230_.1-homo"
d560 v0
  = case coe v0 of
        C71 v1 v2 v3 v4 v5 v6 -> coe v6
        _ -> coe MAlonzo.RTE.mazUnreachableError
name568
  = "Algebra.RingSolver.AlmostCommutativeRing.-raw-almostCommutative\10230"
d568 v0 v1 v2 = du568 v2
du568 v0
  = coe C71 (coe MAlonzo.Code.Function.d68 erased erased)
      (\ v1 v2 ->
         coe du662 v0
           (coe MAlonzo.Code.Function.du68
              (coe du290
                 (coe MAlonzo.Code.Algebra.C259 erased (coe d164 v0) (coe d166 v0)
                    (coe d168 v0)
                    (coe d170 v0)
                    (coe d172 v0))
                 v1
                 v2)))
      (\ v1 v2 ->
         coe du662 v0
           (coe MAlonzo.Code.Function.du68
              (coe du288
                 (coe MAlonzo.Code.Algebra.C259 erased (coe d164 v0) (coe d166 v0)
                    (coe d168 v0)
                    (coe d170 v0)
                    (coe d172 v0))
                 v1
                 v2)))
      (\ v1 ->
         coe du662 v0
           (coe MAlonzo.Code.Function.du68
              (coe du292
                 (coe MAlonzo.Code.Algebra.C259 erased (coe d164 v0) (coe d166 v0)
                    (coe d168 v0)
                    (coe d170 v0)
                    (coe d172 v0))
                 v1)))
      (coe du662 v0
         (coe MAlonzo.Code.Function.du68
            (coe du294
               (coe MAlonzo.Code.Algebra.C259 erased (coe d164 v0) (coe d166 v0)
                  (coe d168 v0)
                  (coe d170 v0)
                  (coe d172 v0)))))
      (coe du662 v0
         (coe MAlonzo.Code.Function.du68
            (coe du296
               (coe MAlonzo.Code.Algebra.C259 erased (coe d164 v0) (coe d166 v0)
                  (coe d168 v0)
                  (coe d170 v0)
                  (coe d172 v0)))))
name662 = "Algebra.RingSolver.AlmostCommutativeRing._._.refl"
d662 v0 v1 v2 = du662 v2
du662 v0 = coe du230 v0
name698
  = "Algebra.RingSolver.AlmostCommutativeRing.Induced-equivalence"
d698 = erased
name718 = "Algebra.RingSolver.AlmostCommutativeRing._._._\8776_"
d718 = erased
name826
  = "Algebra.RingSolver.AlmostCommutativeRing._._.\10214_\10215"
d826 v0 v1 v2 = du826 v0
du826 v0 = coe d550 v0
name832
  = "Algebra.RingSolver.AlmostCommutativeRing.fromCommutativeRing"
d832 v0 v1 v2 = du832 v2
du832 v0
  = coe C33 erased erased (coe MAlonzo.Code.Algebra.d1136 v0)
      (coe MAlonzo.Code.Algebra.d1138 v0)
      (coe MAlonzo.Code.Algebra.d1140 v0)
      (coe MAlonzo.Code.Algebra.d1142 v0)
      (coe MAlonzo.Code.Algebra.d1144 v0)
      (coe C15 (coe du922 v0)
         (coe MAlonzo.Code.Algebra.Structures.d592
            (coe MAlonzo.Code.Algebra.Structures.d746
               (coe MAlonzo.Code.Algebra.Structures.d2050
                  (coe MAlonzo.Code.Algebra.Structures.d2278
                     (coe MAlonzo.Code.Algebra.d1146 v0)))))
         (coe du976 v0)
         (coe du996 v0))
name922
  = "Algebra.RingSolver.AlmostCommutativeRing._._.isCommutativeSemiring"
d922 v0 v1 v2 = du922 v2
du922 v0 = coe MAlonzo.Code.Algebra.du1190 v0
name976
  = "Algebra.RingSolver.AlmostCommutativeRing._._.-\8255*-distrib\737"
d976 v0 v1 v2 = du976 v2
du976 v0
  = coe MAlonzo.Code.Algebra.Properties.Ring.d156 erased erased
      (coe MAlonzo.Code.Algebra.C281 erased erased
         (coe MAlonzo.Code.Algebra.d1136 v0)
         (coe MAlonzo.Code.Algebra.d1138 v0)
         (coe MAlonzo.Code.Algebra.d1140 v0)
         (coe MAlonzo.Code.Algebra.d1142 v0)
         (coe MAlonzo.Code.Algebra.d1144 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2278
            (coe MAlonzo.Code.Algebra.d1146 v0)))
name996
  = "Algebra.RingSolver.AlmostCommutativeRing._._.\8315\185-\8729-comm"
d996 v0 v1 v2 = du996 v2
du996 v0
  = coe MAlonzo.Code.Algebra.Properties.AbelianGroup.d118 erased
      erased
      (coe MAlonzo.Code.Algebra.C103 erased erased
         (coe MAlonzo.Code.Algebra.d1136 v0)
         (coe MAlonzo.Code.Algebra.d1142 v0)
         (coe MAlonzo.Code.Algebra.d1140 v0)
         (coe MAlonzo.Code.Algebra.Structures.d2050
            (coe MAlonzo.Code.Algebra.Structures.d2278
               (coe MAlonzo.Code.Algebra.d1146 v0))))
name1002
  = "Algebra.RingSolver.AlmostCommutativeRing.fromCommutativeSemiring"
d1002 v0 v1 v2 = du1002 v2
du1002 v0
  = coe C33 erased erased (coe MAlonzo.Code.Algebra.d844 v0)
      (coe MAlonzo.Code.Algebra.d846 v0)
      (coe MAlonzo.Code.Function.d68 erased erased)
      (coe MAlonzo.Code.Algebra.d848 v0)
      (coe MAlonzo.Code.Algebra.d850 v0)
      (coe C15 (coe MAlonzo.Code.Algebra.d852 v0)
         (\ v1 v2 -> coe MAlonzo.Code.Function.d68 erased erased)
         (\ v1 v2 ->
            coe du1090 v0
              (coe MAlonzo.Code.Algebra.d846 v0
                 (coe MAlonzo.Code.Function.du68 v1)
                 v2))
         (\ v1 v2 ->
            coe du1090 v0
              (coe MAlonzo.Code.Algebra.d844 v0
                 (coe MAlonzo.Code.Function.du68 v1)
                 (coe MAlonzo.Code.Function.du68 v2))))
name1090 = "Algebra.RingSolver.AlmostCommutativeRing._._.refl"
d1090 v0 v1 v2 = du1090 v2
du1090 v0 = coe MAlonzo.Code.Algebra.du900 v0