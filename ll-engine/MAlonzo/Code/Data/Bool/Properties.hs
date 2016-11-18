{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Data.Bool.Properties where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.FunctionProperties
import qualified MAlonzo.Code.Algebra.Properties.BooleanAlgebra
import qualified
       MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing
import qualified MAlonzo.Code.Algebra.RingSolver.Simple
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Bool
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Data.Sum
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Equivalence
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified
       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
name10 = "Data.Bool.Properties._._DistributesOver_"
d10 = erased
name18 = "Data.Bool.Properties._.Absorptive"
d18 = erased
name30 = "Data.Bool.Properties._.Inverse"
d30 = erased
name52 = "Data.Bool.Properties.\8744-assoc"
d52 = erased
name62 = "Data.Bool.Properties.\8743-assoc"
d62 = erased
name72 = "Data.Bool.Properties.\8744-comm"
d72 = erased
name74 = "Data.Bool.Properties.\8743-comm"
d74 = erased
name76 = "Data.Bool.Properties.distrib-\8743-\8744"
d76 = coe MAlonzo.Code.Data.Product.C30 erased erased
name82 = "Data.Bool.Properties._.dist\737"
d82 = erased
name92 = "Data.Bool.Properties._.dist\691"
d92 = erased
name100 = "Data.Bool.Properties.isCommutativeSemiring-\8744-\8743"
d100
  = coe MAlonzo.Code.Algebra.Structures.C313
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.C25
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
            erased
            erased)
         erased
         erased)
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.C25
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
            erased
            erased)
         erased
         erased)
      (coe MAlonzo.Code.Data.Product.d28 d76)
      erased
name108 = "Data.Bool.Properties.commutativeSemiring-\8744-\8743"
d108
  = coe MAlonzo.Code.Algebra.C239 erased erased
      MAlonzo.Code.Data.Bool.Base.d30
      MAlonzo.Code.Data.Bool.Base.d24
      (coe False)
      (coe True)
      d100
name112 = "Data.Bool.Properties.RingSolver._*H_"
d112
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d118 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name114 = "Data.Bool.Properties.RingSolver._*HN_"
d114
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d120 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name116 = "Data.Bool.Properties.RingSolver._*N_"
d116
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d122 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name118 = "Data.Bool.Properties.RingSolver._*NH_"
d118
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d124 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name124 = "Data.Bool.Properties.RingSolver._*x+H_"
d124
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d130 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name126 = "Data.Bool.Properties.RingSolver._*x+HN_"
d126
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d132 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name128 = "Data.Bool.Properties.RingSolver._+H_"
d128
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d134 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name130 = "Data.Bool.Properties.RingSolver._+N_"
d130
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d136 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name132 = "Data.Bool.Properties.RingSolver._:*_"
d132
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d138 erased erased
      erased
      erased
name134 = "Data.Bool.Properties.RingSolver._:+_"
d134
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d140 erased erased
      erased
      erased
name136 = "Data.Bool.Properties.RingSolver._:-_"
d136
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d142 erased erased
      erased
      erased
name138 = "Data.Bool.Properties.RingSolver._\8860_"
d138 = MAlonzo.Code.Algebra.RingSolver.Simple.du144
name142 = "Data.Bool.Properties.RingSolver._^N_"
d142
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d148 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name144 = "Data.Bool.Properties.RingSolver._\8776H_"
d144 a0 a1 a2 = ()
name146 = "Data.Bool.Properties.RingSolver._\8776N_"
d146 a0 a1 a2 = ()
name148 = "Data.Bool.Properties.RingSolver._\8799H_"
d148
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d154 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name150 = "Data.Bool.Properties.RingSolver._\8799N_"
d150
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d156 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name152 = "Data.Bool.Properties.RingSolver.*H-homo"
d152 = erased
name154 = "Data.Bool.Properties.RingSolver.*HN-homo"
d154 = erased
name156 = "Data.Bool.Properties.RingSolver.*N-homo"
d156 = erased
name158 = "Data.Bool.Properties.RingSolver.*NH-homo"
d158 = erased
name160 = "Data.Bool.Properties.RingSolver.*x+H-homo"
d160 = erased
name162 = "Data.Bool.Properties.RingSolver.*x+HN\8776*x+"
d162 = erased
name164 = "Data.Bool.Properties.RingSolver.+H-homo"
d164 = erased
name166 = "Data.Bool.Properties.RingSolver.+N-homo"
d166 = erased
name168 = "Data.Bool.Properties.RingSolver.-H_"
d168
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d174 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name170 = "Data.Bool.Properties.RingSolver.-H\8255-homo"
d170 = erased
name172 = "Data.Bool.Properties.RingSolver.-N_"
d172
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d178 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name174 = "Data.Bool.Properties.RingSolver.-N\8255-homo"
d174 = erased
name176 = "Data.Bool.Properties.RingSolver.0H"
d176 = MAlonzo.Code.Algebra.RingSolver.Simple.du182
name178 = "Data.Bool.Properties.RingSolver.0N"
d178
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.du184
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
name180 = "Data.Bool.Properties.RingSolver.0N-homo"
d180 = erased
name182 = "Data.Bool.Properties.RingSolver.0\8776\10214\&0\10215"
d182 = erased
name184 = "Data.Bool.Properties.RingSolver.1H"
d184
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d190 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name186 = "Data.Bool.Properties.RingSolver.1N"
d186
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d192 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name188 = "Data.Bool.Properties.RingSolver.1N-homo"
d188 = erased
name192 = "Data.Bool.Properties.RingSolver.HNF"
d192 a0 = ()
name194 = "Data.Bool.Properties.RingSolver.Normal"
d194 a0 = ()
name196 = "Data.Bool.Properties.RingSolver.Op"
d196 = ()
name198 = "Data.Bool.Properties.RingSolver.Polynomial"
d198 a0 = ()
name204 = "Data.Bool.Properties.RingSolver.^N-homo"
d204 = erased
name212 = "Data.Bool.Properties.RingSolver.correct"
d212 = erased
name214 = "Data.Bool.Properties.RingSolver.correct-con"
d214 = erased
name216 = "Data.Bool.Properties.RingSolver.correct-var"
d216 = erased
name218 = "Data.Bool.Properties.RingSolver.normalise"
d218
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d224 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name220 = "Data.Bool.Properties.RingSolver.normalise-con"
d220
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d226 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name222 = "Data.Bool.Properties.RingSolver.normalise-var"
d222
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d228 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name230 = "Data.Bool.Properties.RingSolver.prove"
d230 = erased
name232 = "Data.Bool.Properties.RingSolver.sem"
d232
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.du238
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
name234 = "Data.Bool.Properties.RingSolver.solve"
d234
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d240 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name242 = "Data.Bool.Properties.RingSolver.\8709*x+HN-homo"
d242 = erased
name244 = "Data.Bool.Properties.RingSolver.\10214_\10215"
d244
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.du250
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
name246 = "Data.Bool.Properties.RingSolver.\10214_\10215H"
d246
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d252 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name248 = "Data.Bool.Properties.RingSolver.\10214_\10215H-cong"
d248 = erased
name250 = "Data.Bool.Properties.RingSolver.\10214_\10215N"
d250
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d256 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name252 = "Data.Bool.Properties.RingSolver.\10214_\10215N-cong"
d252 = erased
name254 = "Data.Bool.Properties.RingSolver.\10214_\10215\8595"
d254
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d260 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du1002
         d108)
      MAlonzo.Code.Data.Bool.Base.d42
name298 = "Data.Bool.Properties.distrib-\8744-\8743"
d298 = coe MAlonzo.Code.Data.Product.C30 erased erased
name304 = "Data.Bool.Properties._.dist\737"
d304 = erased
name314 = "Data.Bool.Properties._.dist\691"
d314 = erased
name322 = "Data.Bool.Properties.isCommutativeSemiring-\8743-\8744"
d322
  = coe MAlonzo.Code.Algebra.Structures.C313
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.C25
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
            erased
            erased)
         erased
         erased)
      (coe MAlonzo.Code.Algebra.Structures.C71
         (coe MAlonzo.Code.Algebra.Structures.C25
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
            erased
            erased)
         erased
         erased)
      (coe MAlonzo.Code.Data.Product.d28 d298)
      erased
name330 = "Data.Bool.Properties.commutativeSemiring-\8743-\8744"
d330
  = coe MAlonzo.Code.Algebra.C239 erased erased
      MAlonzo.Code.Data.Bool.Base.d24
      MAlonzo.Code.Data.Bool.Base.d30
      (coe True)
      (coe False)
      d322
name332 = "Data.Bool.Properties.absorptive"
d332 = coe MAlonzo.Code.Data.Product.C30 erased erased
name338 = "Data.Bool.Properties._.abs-\8744-\8743"
d338 = erased
name344 = "Data.Bool.Properties._.abs-\8743-\8744"
d344 = erased
name350 = "Data.Bool.Properties.not-\8743-inverse"
d350
  = coe MAlonzo.Code.Data.Product.C30 erased
      (\ v0 -> coe MAlonzo.Code.Function.du176 erased erased erased)
name356 = "Data.Bool.Properties._.\172x\8743x\8801\8869"
d356 = erased
name360 = "Data.Bool.Properties.not-\8744-inverse"
d360
  = coe MAlonzo.Code.Data.Product.C30 erased
      (\ v0 -> coe MAlonzo.Code.Function.du176 erased erased erased)
name366 = "Data.Bool.Properties._.\172x\8744x\8801\8868"
d366 = erased
name370 = "Data.Bool.Properties.isBooleanAlgebra"
d370
  = coe MAlonzo.Code.Algebra.Structures.C605
      (coe MAlonzo.Code.Algebra.Structures.C573
         (coe MAlonzo.Code.Algebra.Structures.C539
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du50
            erased
            erased
            erased
            erased
            erased
            erased
            d332)
         (coe MAlonzo.Code.Data.Product.d28 d298))
      (coe MAlonzo.Code.Data.Product.d28 d360)
      (coe MAlonzo.Code.Data.Product.d28 d350)
      erased
name372 = "Data.Bool.Properties.booleanAlgebra"
d372
  = coe MAlonzo.Code.Algebra.C375 erased erased
      MAlonzo.Code.Data.Bool.Base.d30
      MAlonzo.Code.Data.Bool.Base.d24
      MAlonzo.Code.Data.Bool.Base.d6
      (coe True)
      (coe False)
      d370
name378 = "Data.Bool.Properties.xor-is-ok"
d378 = erased
name404 = "Data.Bool.Properties._.CS.identity"
d404 v0 = du404
du404 = coe MAlonzo.Code.Algebra.du862 d108
name425 = "Data.Bool.Properties..absurdlambda"
d425 = erased
name429 = "Data.Bool.Properties..absurdlambda"
d429 = erased
name443 = "Data.Bool.Properties..absurdlambda"
d443 = erased
name447 = "Data.Bool.Properties..absurdlambda"
d447 = erased
name488 = "Data.Bool.Properties.commutativeRing-xor-\8743"
d488 = d570
name515 = "Data.Bool.Properties..absurdlambda"
d515 = erased
name549 = "Data.Bool.Properties..absurdlambda"
d549 = erased
name558 = "Data.Bool.Properties._._.XorRing.commutativeRing"
d558
  = coe MAlonzo.Code.Algebra.Properties.BooleanAlgebra.d528 erased
      erased
      d372
name570 = "Data.Bool.Properties._._.commutativeRing"
d570 = coe d558 MAlonzo.Code.Data.Bool.Base.d36 erased
name582 = "Data.Bool.Properties.XorRingSolver._*H_"
d582
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d118 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name584 = "Data.Bool.Properties.XorRingSolver._*HN_"
d584
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d120 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name586 = "Data.Bool.Properties.XorRingSolver._*N_"
d586
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d122 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name588 = "Data.Bool.Properties.XorRingSolver._*NH_"
d588
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d124 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name594 = "Data.Bool.Properties.XorRingSolver._*x+H_"
d594
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d130 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name596 = "Data.Bool.Properties.XorRingSolver._*x+HN_"
d596
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d132 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name598 = "Data.Bool.Properties.XorRingSolver._+H_"
d598
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d134 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name600 = "Data.Bool.Properties.XorRingSolver._+N_"
d600
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d136 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name602 = "Data.Bool.Properties.XorRingSolver._:*_"
d602
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d138 erased erased
      erased
      erased
name604 = "Data.Bool.Properties.XorRingSolver._:+_"
d604
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d140 erased erased
      erased
      erased
name606 = "Data.Bool.Properties.XorRingSolver._:-_"
d606
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d142 erased erased
      erased
      erased
name608 = "Data.Bool.Properties.XorRingSolver._\8860_"
d608 = MAlonzo.Code.Algebra.RingSolver.Simple.du144
name612 = "Data.Bool.Properties.XorRingSolver._^N_"
d612
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d148 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name614 = "Data.Bool.Properties.XorRingSolver._\8776H_"
d614 a0 a1 a2 = ()
name616 = "Data.Bool.Properties.XorRingSolver._\8776N_"
d616 a0 a1 a2 = ()
name618 = "Data.Bool.Properties.XorRingSolver._\8799H_"
d618
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d154 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name620 = "Data.Bool.Properties.XorRingSolver._\8799N_"
d620
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d156 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name622 = "Data.Bool.Properties.XorRingSolver.*H-homo"
d622 = erased
name624 = "Data.Bool.Properties.XorRingSolver.*HN-homo"
d624 = erased
name626 = "Data.Bool.Properties.XorRingSolver.*N-homo"
d626 = erased
name628 = "Data.Bool.Properties.XorRingSolver.*NH-homo"
d628 = erased
name630 = "Data.Bool.Properties.XorRingSolver.*x+H-homo"
d630 = erased
name632 = "Data.Bool.Properties.XorRingSolver.*x+HN\8776*x+"
d632 = erased
name634 = "Data.Bool.Properties.XorRingSolver.+H-homo"
d634 = erased
name636 = "Data.Bool.Properties.XorRingSolver.+N-homo"
d636 = erased
name638 = "Data.Bool.Properties.XorRingSolver.-H_"
d638
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d174 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name640 = "Data.Bool.Properties.XorRingSolver.-H\8255-homo"
d640 = erased
name642 = "Data.Bool.Properties.XorRingSolver.-N_"
d642
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d178 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name644 = "Data.Bool.Properties.XorRingSolver.-N\8255-homo"
d644 = erased
name646 = "Data.Bool.Properties.XorRingSolver.0H"
d646 = MAlonzo.Code.Algebra.RingSolver.Simple.du182
name648 = "Data.Bool.Properties.XorRingSolver.0N"
d648
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.du184
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
name650 = "Data.Bool.Properties.XorRingSolver.0N-homo"
d650 = erased
name652
  = "Data.Bool.Properties.XorRingSolver.0\8776\10214\&0\10215"
d652 = erased
name654 = "Data.Bool.Properties.XorRingSolver.1H"
d654
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d190 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name656 = "Data.Bool.Properties.XorRingSolver.1N"
d656
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d192 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name658 = "Data.Bool.Properties.XorRingSolver.1N-homo"
d658 = erased
name662 = "Data.Bool.Properties.XorRingSolver.HNF"
d662 a0 = ()
name664 = "Data.Bool.Properties.XorRingSolver.Normal"
d664 a0 = ()
name666 = "Data.Bool.Properties.XorRingSolver.Op"
d666 = ()
name668 = "Data.Bool.Properties.XorRingSolver.Polynomial"
d668 a0 = ()
name674 = "Data.Bool.Properties.XorRingSolver.^N-homo"
d674 = erased
name682 = "Data.Bool.Properties.XorRingSolver.correct"
d682 = erased
name684 = "Data.Bool.Properties.XorRingSolver.correct-con"
d684 = erased
name686 = "Data.Bool.Properties.XorRingSolver.correct-var"
d686 = erased
name688 = "Data.Bool.Properties.XorRingSolver.normalise"
d688
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d224 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name690 = "Data.Bool.Properties.XorRingSolver.normalise-con"
d690
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d226 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name692 = "Data.Bool.Properties.XorRingSolver.normalise-var"
d692
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d228 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name700 = "Data.Bool.Properties.XorRingSolver.prove"
d700 = erased
name702 = "Data.Bool.Properties.XorRingSolver.sem"
d702
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.du238
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
name704 = "Data.Bool.Properties.XorRingSolver.solve"
d704
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d240 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name712 = "Data.Bool.Properties.XorRingSolver.\8709*x+HN-homo"
d712 = erased
name714 = "Data.Bool.Properties.XorRingSolver.\10214_\10215"
d714
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.du250
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
name716 = "Data.Bool.Properties.XorRingSolver.\10214_\10215H"
d716
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d252 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name718 = "Data.Bool.Properties.XorRingSolver.\10214_\10215H-cong"
d718 = erased
name720 = "Data.Bool.Properties.XorRingSolver.\10214_\10215N"
d720
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d256 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name722 = "Data.Bool.Properties.XorRingSolver.\10214_\10215N-cong"
d722 = erased
name724 = "Data.Bool.Properties.XorRingSolver.\10214_\10215\8595"
d724
  = coe MAlonzo.Code.Algebra.RingSolver.Simple.d260 () ()
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du832
         d488)
      MAlonzo.Code.Data.Bool.Base.d42
name768 = "Data.Bool.Properties.not-involutive"
d768 = erased
name774 = "Data.Bool.Properties.not-\172"
d774 = erased
name780 = "Data.Bool.Properties.\172-not"
d780 = erased
name792 = "Data.Bool.Properties.\8660\8594\8801"
d792 = erased
name808 = "Data.Bool.Properties.T-\8801"
d808 v0
  = case coe v0 of
        False -> coe MAlonzo.Code.Function.Equivalence.du56 erased erased
                   erased
                   erased
        True -> coe MAlonzo.Code.Function.Equivalence.du56 erased erased
                  (coe MAlonzo.Code.Function.d80 erased erased erased erased erased)
                  (coe MAlonzo.Code.Function.d80 erased erased erased erased erased)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name812 = "Data.Bool.Properties.T-not-\8801"
d812 v0
  = case coe v0 of
        False -> coe MAlonzo.Code.Function.Equivalence.du56 erased erased
                   (coe MAlonzo.Code.Function.d80 erased erased erased erased erased)
                   (coe MAlonzo.Code.Function.d80 erased erased erased erased erased)
        True -> coe MAlonzo.Code.Function.Equivalence.du56 erased erased
                  erased
                  erased
        _ -> coe MAlonzo.RTE.mazUnreachableError
name818 = "Data.Bool.Properties.T-\8743"
d818 v0 v1
  = case coe v0 of
        False -> coe MAlonzo.Code.Function.Equivalence.du56 erased erased
                   erased
                   MAlonzo.Code.Data.Product.d26
        True -> case coe v1 of
                    False -> coe MAlonzo.Code.Function.Equivalence.du56 erased erased
                               erased
                               MAlonzo.Code.Data.Product.d28
                    True -> coe MAlonzo.Code.Function.Equivalence.du56 erased erased
                              (coe MAlonzo.Code.Function.d80 erased erased erased erased
                                 (coe MAlonzo.Code.Data.Product.C30 erased erased))
                              (coe MAlonzo.Code.Function.d80 erased erased erased erased erased)
                    _ -> coe MAlonzo.RTE.mazUnreachableError
        _ -> coe MAlonzo.RTE.mazUnreachableError
name824 = "Data.Bool.Properties.T-\8744"
d824 v0 v1
  = case coe v0 of
        False -> case coe v1 of
                     False -> coe MAlonzo.Code.Function.Equivalence.du56 erased erased
                                (coe Left)
                                (coe MAlonzo.Code.Data.Sum.d48 erased erased erased erased erased
                                   erased
                                   (coe MAlonzo.Code.Function.d68 erased erased)
                                   (coe MAlonzo.Code.Function.d68 erased erased))
                     True -> coe MAlonzo.Code.Function.Equivalence.du56 erased erased
                               (coe Right)
                               (coe MAlonzo.Code.Function.d80 erased erased erased erased erased)
                     _ -> coe MAlonzo.RTE.mazUnreachableError
        True -> coe MAlonzo.Code.Function.Equivalence.du56 erased erased
                  (coe Left)
                  (coe MAlonzo.Code.Function.d80 erased erased erased erased erased)
        _ -> coe MAlonzo.RTE.mazUnreachableError
name834 = "Data.Bool.Properties.proof-irrelevance"
d834 = erased
name852 = "Data.Bool.Properties.push-function-into-if"
d852 = erased