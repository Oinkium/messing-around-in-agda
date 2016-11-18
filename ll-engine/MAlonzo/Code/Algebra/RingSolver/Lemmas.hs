{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Algebra.RingSolver.Lemmas where
import MAlonzo.RTE (coe, erased)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.Morphism
import qualified
       MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Function
import qualified MAlonzo.Code.Relation.Binary.EqReasoning
import qualified MAlonzo.Code.Relation.Binary.PreorderReasoning
name34 = "Algebra.RingSolver.Lemmas._._*_"
d34 v0 v1 v2 v3 v4 v5 = du34 v4
du34 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
name36 = "Algebra.RingSolver.Lemmas._._+_"
d36 v0 v1 v2 v3 v4 v5 = du36 v4
du36 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
name38 = "Algebra.RingSolver.Lemmas._._\8776_"
d38 = erased
name40 = "Algebra.RingSolver.Lemmas._.assoc"
d40 v0 v1 v2 v3 v4 v5 = du40 v4
du40 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du178
      v0
name42 = "Algebra.RingSolver.Lemmas._.comm"
d42 v0 v1 v2 v3 v4 v5 = du42 v4
du42 v0
  = coe MAlonzo.Code.Algebra.Structures.d410
      (coe MAlonzo.Code.Algebra.Structures.d1768
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d60
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d174
               v0)))
name46 = "Algebra.RingSolver.Lemmas._.\8729-cong"
d46 v0 v1 v2 v3 v4 v5 = du46 v4
du46 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du182
      v0
name48 = "Algebra.RingSolver.Lemmas._.identity"
d48 v0 v1 v2 v3 v4 v5 = du48 v4
du48 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du184
      v0
name60 = "Algebra.RingSolver.Lemmas._.assoc"
d60 v0 v1 v2 v3 v4 v5 = du60 v4
du60 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du192
      v0
name62 = "Algebra.RingSolver.Lemmas._.comm"
d62 v0 v1 v2 v3 v4 v5 = du62 v4
du62 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du194
      v0
name66 = "Algebra.RingSolver.Lemmas._.\8729-cong"
d66 v0 v1 v2 v3 v4 v5 = du66 v4
du66 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du196
      v0
name68 = "Algebra.RingSolver.Lemmas._.identity"
d68 v0 v1 v2 v3 v4 v5 = du68 v4
du68 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du198
      v0
name80 = "Algebra.RingSolver.Lemmas._.-_"
d80 v0 v1 v2 v3 v4 v5 = du80 v4
du80 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d168 v0
name82 = "Algebra.RingSolver.Lemmas._.-\8255*-distrib\737"
d82 v0 v1 v2 v3 v4 v5 = du82 v4
du82 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d68
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d174 v0)
name86 = "Algebra.RingSolver.Lemmas._.-\8255cong"
d86 v0 v1 v2 v3 v4 v5 = du86 v4
du86 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d62
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d174 v0)
name88 = "Algebra.RingSolver.Lemmas._.0#"
d88 v0 v1 v2 v3 v4 v5 = du88 v4
du88 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0
name90 = "Algebra.RingSolver.Lemmas._.1#"
d90 v0 v1 v2 v3 v4 v5 = du90 v4
du90 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d172 v0
name96 = "Algebra.RingSolver.Lemmas._.distrib"
d96 v0 v1 v2 v3 v4 v5 = du96 v4
du96 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du212
      v0
name118 = "Algebra.RingSolver.Lemmas._.refl"
d118 v0 v1 v2 v3 v4 v5 = du118 v4
du118 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du230
      v0
name124 = "Algebra.RingSolver.Lemmas._.setoid"
d124 v0 v1 v2 v3 v4 v5 = du124 v4
du124 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du260
      v0
name126 = "Algebra.RingSolver.Lemmas._.sym"
d126 v0 v1 v2 v3 v4 v5 = du126 v4
du126 v0
  = coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.du234
      v0
name132 = "Algebra.RingSolver.Lemmas._.zero\737"
d132 v0 v1 v2 v3 v4 v5 = du132 v4
du132 v0
  = coe MAlonzo.Code.Algebra.Structures.d1772
      (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d60
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d174
            v0))
name152 = "Algebra.RingSolver.Lemmas._._\8718"
d152 v0 v1 v2 v3 v4 v5 = du152 v4
du152 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.d38 erased erased
      (coe du124 v0)
name154 = "Algebra.RingSolver.Lemmas._._\8764\10216_\10217_"
d154 v0 v1 v2 v3 v4 v5 = du154 v4
du154 v0
  = coe MAlonzo.Code.Relation.Binary.EqReasoning.du40 (coe du124 v0)
name176 = "Algebra.RingSolver.Lemmas.lemma\8320"
d176 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du176 v4 v6 v7 v8 v9
du176 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0 (coe du36 v0 (coe du34 v0 (coe du36 v0 v1 v2) v4) v3)
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  v1
                  v4)
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  v2
                  v4))
            v3)
         (coe du36 v0 (coe du34 v0 v1 v4)
            (coe du36 v0 (coe du34 v0 v2 v4) v3))
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Data.Product.d28 (coe du96 v0) v4 v1 v2)
            (coe du66 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     v1
                     v2)
                  v4)
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v1
                     v4)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v2
                     v4))
               v3
               v3)
            (coe du118 v0 v3))
         (coe du154 v0
            (coe du36 v0 (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v4))
               v3)
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
               (coe du34 v0 v1 v4)
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe du34 v0 v2 v4)
                  v3))
            (coe du36 v0 (coe du34 v0 v1 v4)
               (coe du36 v0 (coe du34 v0 v2 v4) v3))
            (coe du60 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v4) v3)
            (coe du152 v0
               (coe du36 v0 (coe du34 v0 v1 v4)
                  (coe du36 v0 (coe du34 v0 v2 v4) v3)))))
name196 = "Algebra.RingSolver.Lemmas.lemma\8321"
d196 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du196 v4 v6 v7 v8 v9 v10
du196 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0
         (coe du36 v0 (coe du34 v0 (coe du36 v0 v1 v2) v5)
            (coe du36 v0 v3 v4))
         (coe du36 v0 (coe du34 v0 v1 v5)
            (coe du36 v0 (coe du34 v0 v2 v5) (coe du36 v0 v3 v4)))
         (coe du36 v0 (coe du36 v0 (coe du34 v0 v1 v5) v3)
            (coe du36 v0 (coe du34 v0 v2 v5) v4))
         (coe du176 v0 v1 v2 (coe du36 v0 v3 v4) v5)
         (coe du154 v0
            (coe du36 v0 (coe du34 v0 v1 v5)
               (coe du36 v0 (coe du34 v0 v2 v5) (coe du36 v0 v3 v4)))
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
               (coe du34 v0 v1 v5)
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe du34 v0 v2 v5)
                     v3)
                  v4))
            (coe du36 v0 (coe du36 v0 (coe du34 v0 v1 v5) v3)
               (coe du36 v0 (coe du34 v0 v2 v5) v4))
            (coe MAlonzo.Code.Function.du176 (coe du118 v0 (coe du34 v0 v1 v5))
               (coe du66 v0 (coe du34 v0 v1 v5) (coe du34 v0 v1 v5)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe du34 v0 v2 v5)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        v3
                        v4))
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe du34 v0 v2 v5)
                        v3)
                     v4))
               (coe du126 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe du34 v0 v2 v5)
                        v3)
                     v4)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe du34 v0 v2 v5)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        v3
                        v4))
                  (coe du60 v0 (coe du34 v0 v2 v5) v3 v4)))
            (coe du154 v0
               (coe du36 v0 (coe du34 v0 v1 v5)
                  (coe du36 v0 (coe du36 v0 (coe du34 v0 v2 v5) v3) v4))
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe du34 v0 v1 v5)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        v3
                        (coe du34 v0 v2 v5))
                     v4))
               (coe du36 v0 (coe du36 v0 (coe du34 v0 v1 v5) v3)
                  (coe du36 v0 (coe du34 v0 v2 v5) v4))
               (coe MAlonzo.Code.Function.du176 (coe du118 v0 (coe du34 v0 v1 v5))
                  (coe du66 v0 (coe du34 v0 v1 v5) (coe du34 v0 v1 v5)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 v2 v5)
                           v3)
                        v4)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           v3
                           (coe du34 v0 v2 v5))
                        v4))
                  (coe MAlonzo.Code.Function.du176
                     (coe du62 v0 (coe du34 v0 v2 v5) v3)
                     (coe du66 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 v2 v5)
                           v3)
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           v3
                           (coe du34 v0 v2 v5))
                        v4
                        v4)
                     (coe du118 v0 v4)))
               (coe du154 v0
                  (coe du36 v0 (coe du34 v0 v1 v5)
                     (coe du36 v0 (coe du36 v0 v3 (coe du34 v0 v2 v5)) v4))
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe du34 v0 v1 v5)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        v3
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 v2 v5)
                           v4)))
                  (coe du36 v0 (coe du36 v0 (coe du34 v0 v1 v5) v3)
                     (coe du36 v0 (coe du34 v0 v2 v5) v4))
                  (coe MAlonzo.Code.Function.du176 (coe du118 v0 (coe du34 v0 v1 v5))
                     (coe du66 v0 (coe du34 v0 v1 v5) (coe du34 v0 v1 v5)
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                              v3
                              (coe du34 v0 v2 v5))
                           v4)
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           v3
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                              (coe du34 v0 v2 v5)
                              v4)))
                     (coe du60 v0 v3 (coe du34 v0 v2 v5) v4))
                  (coe du154 v0
                     (coe du36 v0 (coe du34 v0 v1 v5)
                        (coe du36 v0 v3 (coe du36 v0 (coe du34 v0 v2 v5) v4)))
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 v1 v5)
                           v3)
                        (coe du36 v0 (coe du34 v0 v2 v5) v4))
                     (coe du36 v0 (coe du36 v0 (coe du34 v0 v1 v5) v3)
                        (coe du36 v0 (coe du34 v0 v2 v5) v4))
                     (coe MAlonzo.Code.Function.du158
                        (coe du126 v0
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                 (coe du34 v0 v1 v5)
                                 v3)
                              (coe du36 v0 (coe du34 v0 v2 v5) v4))
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                              (coe du34 v0 v1 v5)
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                 v3
                                 (coe du36 v0 (coe du34 v0 v2 v5) v4))))
                        (coe du60 v0 (coe du34 v0 v1 v5) v3
                           (coe du36 v0 (coe du34 v0 v2 v5) v4)))
                     (coe du152 v0
                        (coe du36 v0 (coe du36 v0 (coe du34 v0 v1 v5) v3)
                           (coe du36 v0 (coe du34 v0 v2 v5) v4))))))))
name216 = "Algebra.RingSolver.Lemmas.lemma\8322"
d216 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du216 v4 v6 v7 v8 v9
du216 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0
         (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v3) v4)
            (coe du34 v0 v2 v3))
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
            (coe du34 v0 (coe du34 v0 v1 v4) v3)
            (coe du34 v0 v2 v3))
         (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) v2) v3)
         (coe MAlonzo.Code.Function.du176 (coe du230 v0 v1 v3 v4)
            (coe du66 v0 (coe du34 v0 (coe du34 v0 v1 v3) v4)
               (coe du34 v0 (coe du34 v0 v1 v4) v3)
               (coe du34 v0 v2 v3)
               (coe du34 v0 v2 v3))
            (coe du118 v0 (coe du34 v0 v2 v3)))
         (coe du154 v0
            (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v4) v3)
               (coe du34 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe du34 v0 v1 v4)
                  v2)
               v3)
            (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) v2) v3)
            (coe MAlonzo.Code.Function.du158
               (coe du126 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe du34 v0 v1 v4)
                        v2)
                     v3)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe du34 v0 v1 v4)
                        v3)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v2
                        v3)))
               (coe MAlonzo.Code.Data.Product.d28 (coe du96 v0) v3
                  (coe du34 v0 v1 v4)
                  v2))
            (coe du152 v0
               (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) v2) v3))))
name230 = "Algebra.RingSolver.Lemmas._.lem"
d230 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du230 v4 v6 v8 v9
du230 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0 (coe du34 v0 (coe du34 v0 v1 v2) v3)
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
            v1
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               v2
               v3))
         (coe du34 v0 (coe du34 v0 v1 v3) v2)
         (coe du40 v0 v1 v2 v3)
         (coe du154 v0 (coe du34 v0 v1 (coe du34 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               v1
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  v3
                  v2))
            (coe du34 v0 (coe du34 v0 v1 v3) v2)
            (coe MAlonzo.Code.Function.du176 (coe du118 v0 v1)
               (coe du46 v0 v1 v1
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v2
                     v3)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v3
                     v2))
               (coe du42 v0 v2 v3))
            (coe du154 v0 (coe du34 v0 v1 (coe du34 v0 v3 v2))
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v1
                     v3)
                  v2)
               (coe du34 v0 (coe du34 v0 v1 v3) v2)
               (coe MAlonzo.Code.Function.du158
                  (coe du126 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                           v1
                           v3)
                        v2)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v1
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                           v3
                           v2)))
                  (coe du40 v0 v1 v3 v2))
               (coe du152 v0 (coe du34 v0 (coe du34 v0 v1 v3) v2)))))
name240 = "Algebra.RingSolver.Lemmas.lemma\8323"
d240 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du240 v4 v6 v7 v8 v9
du240 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0
         (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v2) v4)
            (coe du34 v0 v1 v3))
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               v1
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  v2
                  v4))
            (coe du34 v0 v1 v3))
         (coe du34 v0 v1 (coe du36 v0 (coe du34 v0 v2 v4) v3))
         (coe MAlonzo.Code.Function.du176 (coe du40 v0 v1 v2 v4)
            (coe du66 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v1
                     v2)
                  v4)
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  v1
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v2
                     v4))
               (coe du34 v0 v1 v3)
               (coe du34 v0 v1 v3))
            (coe du118 v0 (coe du34 v0 v1 v3)))
         (coe du154 v0
            (coe du36 v0 (coe du34 v0 v1 (coe du34 v0 v2 v4))
               (coe du34 v0 v1 v3))
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               v1
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe du34 v0 v2 v4)
                  v3))
            (coe du34 v0 v1 (coe du36 v0 (coe du34 v0 v2 v4) v3))
            (coe MAlonzo.Code.Function.du158
               (coe du126 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v1
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe du34 v0 v2 v4)
                        v3))
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v1
                        (coe du34 v0 v2 v4))
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v1
                        v3)))
               (coe MAlonzo.Code.Data.Product.d26 (coe du96 v0) v1
                  (coe du34 v0 v2 v4)
                  v3))
            (coe du152 v0
               (coe du34 v0 v1 (coe du36 v0 (coe du34 v0 v2 v4) v3)))))
name260 = "Algebra.RingSolver.Lemmas.lemma\8324"
d260 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du260 v4 v6 v7 v8 v9 v10
du260 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0
         (coe du36 v0
            (coe du34 v0
               (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5)
                  (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3)))
               v5)
            (coe du34 v0 v2 v4))
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe du34 v0 (coe du34 v0 v1 v3) v5)
                  v5)
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3))
                  v5))
            (coe du34 v0 v2 v4))
         (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v5) v2)
            (coe du36 v0 (coe du34 v0 v3 v5) v4))
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Data.Product.d28 (coe du96 v0) v5
               (coe du34 v0 (coe du34 v0 v1 v3) v5)
               (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3)))
            (coe du66 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe du34 v0 (coe du34 v0 v1 v3) v5)
                     (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3)))
                  v5)
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     (coe du34 v0 (coe du34 v0 v1 v3) v5)
                     v5)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3))
                     v5))
               (coe du34 v0 v2 v4)
               (coe du34 v0 v2 v4))
            (coe du118 v0 (coe du34 v0 v2 v4)))
         (coe du154 v0
            (coe du36 v0
               (coe du36 v0 (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                  (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3))
                     v5))
               (coe du34 v0 v2 v4))
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe du34 v0 v1 v4)
                        (coe du34 v0 v2 v3))
                     v5))
               (coe du34 v0 v2 v4))
            (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v5) v2)
               (coe du36 v0 (coe du34 v0 v3 v5) v4))
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Function.du176
                  (coe du118 v0
                     (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5))
                  (coe du66 v0 (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                     (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 v1 v4)
                           (coe du34 v0 v2 v3))
                        v5)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 v1 v4)
                           (coe du34 v0 v2 v3))
                        v5))
                  (coe MAlonzo.Code.Function.du176
                     (coe MAlonzo.Code.Function.du176 (coe du118 v0 (coe du34 v0 v1 v4))
                        (coe du66 v0 (coe du34 v0 v1 v4) (coe du34 v0 v1 v4)
                           (coe du34 v0 v2 v3)
                           (coe du34 v0 v2 v3))
                        (coe du118 v0 (coe du34 v0 v2 v3)))
                     (coe du46 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 v1 v4)
                           (coe du34 v0 v2 v3))
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 v1 v4)
                           (coe du34 v0 v2 v3))
                        v5
                        v5)
                     (coe du118 v0 v5)))
               (coe du66 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 v1 v4)
                           (coe du34 v0 v2 v3))
                        v5))
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 v1 v4)
                           (coe du34 v0 v2 v3))
                        v5))
                  (coe du34 v0 v2 v4)
                  (coe du34 v0 v2 v4))
               (coe du118 v0 (coe du34 v0 v2 v4)))
            (coe du154 v0
               (coe du36 v0
                  (coe du36 v0 (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                     (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3))
                        v5))
                  (coe du34 v0 v2 v4))
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3))
                        v5)
                     (coe du34 v0 v2 v4)))
               (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v5) v2)
                  (coe du36 v0 (coe du34 v0 v3 v5) v4))
               (coe du60 v0 (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                  (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3))
                     v5)
                  (coe du34 v0 v2 v4))
               (coe du154 v0
                  (coe du36 v0 (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                     (coe du36 v0
                        (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3))
                           v5)
                        (coe du34 v0 v2 v4)))
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
                           (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                        (coe du34 v0 v2 v4)))
                  (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v5) v2)
                     (coe du36 v0 (coe du34 v0 v3 v5) v4))
                  (coe MAlonzo.Code.Function.du176 (coe du278 v0 v1 v3 v5)
                     (coe du66 v0 (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v5) v5)
                        (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3))
                              v5)
                           (coe du34 v0 v2 v4))
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
                              (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                           (coe du34 v0 v2 v4)))
                     (coe MAlonzo.Code.Function.du176 (coe du280 v0 v1 v2 v3 v4 v5)
                        (coe du66 v0
                           (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3))
                              v5)
                           (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
                              (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                           (coe du34 v0 v2 v4)
                           (coe du34 v0 v2 v4))
                        (coe du118 v0 (coe du34 v0 v2 v4))))
                  (coe du154 v0
                     (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                        (coe du36 v0
                           (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
                              (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                           (coe du34 v0 v2 v4)))
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe du34 v0 (coe du34 v0 v1 v5) v4)
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                              (coe du34 v0 v2 (coe du34 v0 v3 v5))
                              (coe du34 v0 v2 v4))))
                     (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v5) v2)
                        (coe du36 v0 (coe du34 v0 v3 v5) v4))
                     (coe MAlonzo.Code.Function.du176
                        (coe du118 v0
                           (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5)))
                        (coe du66 v0 (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                           (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                 (coe du34 v0 (coe du34 v0 v1 v5) v4)
                                 (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                              (coe du34 v0 v2 v4))
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                              (coe du34 v0 (coe du34 v0 v1 v5) v4)
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                 (coe du34 v0 v2 (coe du34 v0 v3 v5))
                                 (coe du34 v0 v2 v4))))
                        (coe du60 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
                           (coe du34 v0 v2 (coe du34 v0 v3 v5))
                           (coe du34 v0 v2 v4)))
                     (coe du154 v0
                        (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                           (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
                              (coe du36 v0 (coe du34 v0 v2 (coe du34 v0 v3 v5))
                                 (coe du34 v0 v2 v4))))
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                              (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                              (coe du34 v0 (coe du34 v0 v1 v5) v4))
                           (coe du36 v0 (coe du34 v0 v2 (coe du34 v0 v3 v5))
                              (coe du34 v0 v2 v4)))
                        (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v5) v2)
                           (coe du36 v0 (coe du34 v0 v3 v5) v4))
                        (coe MAlonzo.Code.Function.du158
                           (coe du126 v0
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                 (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                    (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                                    (coe du34 v0 (coe du34 v0 v1 v5) v4))
                                 (coe du36 v0 (coe du34 v0 v2 (coe du34 v0 v3 v5))
                                    (coe du34 v0 v2 v4)))
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                 (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                                 (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                    (coe du34 v0 (coe du34 v0 v1 v5) v4)
                                    (coe du36 v0 (coe du34 v0 v2 (coe du34 v0 v3 v5))
                                       (coe du34 v0 v2 v4)))))
                           (coe du60 v0 (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                              (coe du34 v0 (coe du34 v0 v1 v5) v4)
                              (coe du36 v0 (coe du34 v0 v2 (coe du34 v0 v3 v5))
                                 (coe du34 v0 v2 v4))))
                        (coe du154 v0
                           (coe du36 v0
                              (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) (coe du34 v0 v3 v5))
                                 (coe du34 v0 (coe du34 v0 v1 v5) v4))
                              (coe du36 v0 (coe du34 v0 v2 (coe du34 v0 v3 v5))
                                 (coe du34 v0 v2 v4)))
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                                 (coe du34 v0 v1 v5)
                                 (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                    (coe du34 v0 v3 v5)
                                    v4))
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                                 v2
                                 (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                    (coe du34 v0 v3 v5)
                                    v4)))
                           (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v5) v2)
                              (coe du36 v0 (coe du34 v0 v3 v5) v4))
                           (coe MAlonzo.Code.Function.du158
                              (coe du126 v0
                                 (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                    (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                       v0
                                       (coe du34 v0 v1 v5)
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                          v0
                                          (coe du34 v0 v3 v5)
                                          v4))
                                    (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                       v0
                                       v2
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                          v0
                                          (coe du34 v0 v3 v5)
                                          v4)))
                                 (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                    (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                          v0
                                          (coe du34 v0 v1 v5)
                                          (coe du34 v0 v3 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                          v0
                                          (coe du34 v0 v1 v5)
                                          v4))
                                    (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                          v0
                                          v2
                                          (coe du34 v0 v3 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                          v0
                                          v2
                                          v4))))
                              (coe MAlonzo.Code.Function.du176
                                 (coe MAlonzo.Code.Data.Product.d26 (coe du96 v0)
                                    (coe du34 v0 v1 v5)
                                    (coe du34 v0 v3 v5)
                                    v4)
                                 (coe du66 v0
                                    (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                       v0
                                       (coe du34 v0 v1 v5)
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                          v0
                                          (coe du34 v0 v3 v5)
                                          v4))
                                    (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                          v0
                                          (coe du34 v0 v1 v5)
                                          (coe du34 v0 v3 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                          v0
                                          (coe du34 v0 v1 v5)
                                          v4))
                                    (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                       v0
                                       v2
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                          v0
                                          (coe du34 v0 v3 v5)
                                          v4))
                                    (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                          v0
                                          v2
                                          (coe du34 v0 v3 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                          v0
                                          v2
                                          v4)))
                                 (coe MAlonzo.Code.Data.Product.d26 (coe du96 v0) v2
                                    (coe du34 v0 v3 v5)
                                    v4)))
                           (coe du154 v0
                              (coe du36 v0
                                 (coe du34 v0 (coe du34 v0 v1 v5)
                                    (coe du36 v0 (coe du34 v0 v3 v5) v4))
                                 (coe du34 v0 v2 (coe du36 v0 (coe du34 v0 v3 v5) v4)))
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                                 (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                                    (coe du34 v0 v1 v5)
                                    v2)
                                 (coe du36 v0 (coe du34 v0 v3 v5) v4))
                              (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v5) v2)
                                 (coe du36 v0 (coe du34 v0 v3 v5) v4))
                              (coe MAlonzo.Code.Function.du158
                                 (coe du126 v0
                                    (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                          v0
                                          (coe du34 v0 v1 v5)
                                          v2)
                                       (coe du36 v0 (coe du34 v0 v3 v5) v4))
                                    (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164
                                       v0
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                          v0
                                          (coe du34 v0 v1 v5)
                                          (coe du36 v0 (coe du34 v0 v3 v5) v4))
                                       (coe
                                          MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166
                                          v0
                                          v2
                                          (coe du36 v0 (coe du34 v0 v3 v5) v4))))
                                 (coe MAlonzo.Code.Data.Product.d28 (coe du96 v0)
                                    (coe du36 v0 (coe du34 v0 v3 v5) v4)
                                    (coe du34 v0 v1 v5)
                                    v2))
                              (coe du152 v0
                                 (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v5) v2)
                                    (coe du36 v0 (coe du34 v0 v3 v5) v4)))))))))))
name276 = "Algebra.RingSolver.Lemmas._.lem\8321\8242"
d276 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du276 v4 v6 v8 v10
du276 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0 (coe du34 v0 (coe du34 v0 v1 v2) v3)
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
            v1
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               v2
               v3))
         (coe du34 v0 (coe du34 v0 v1 v3) v2)
         (coe du40 v0 v1 v2 v3)
         (coe du154 v0 (coe du34 v0 v1 (coe du34 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               v1
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  v3
                  v2))
            (coe du34 v0 (coe du34 v0 v1 v3) v2)
            (coe MAlonzo.Code.Function.du176 (coe du118 v0 v1)
               (coe du46 v0 v1 v1
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v2
                     v3)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v3
                     v2))
               (coe du42 v0 v2 v3))
            (coe du154 v0 (coe du34 v0 v1 (coe du34 v0 v3 v2))
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v1
                     v3)
                  v2)
               (coe du34 v0 (coe du34 v0 v1 v3) v2)
               (coe MAlonzo.Code.Function.du158
                  (coe du126 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                           v1
                           v3)
                        v2)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v1
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                           v3
                           v2)))
                  (coe du40 v0 v1 v3 v2))
               (coe du152 v0 (coe du34 v0 (coe du34 v0 v1 v3) v2)))))
name278 = "Algebra.RingSolver.Lemmas._.lem\8321"
d278 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du278 v4 v6 v8 v10
du278 v0 v1 v2 v3
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0 (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v2) v3) v3)
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
            (coe du34 v0 (coe du34 v0 v1 v3) v2)
            v3)
         (coe du34 v0 (coe du34 v0 v1 v3) (coe du34 v0 v2 v3))
         (coe MAlonzo.Code.Function.du176 (coe du276 v0 v1 v2 v3)
            (coe du46 v0 (coe du34 v0 (coe du34 v0 v1 v2) v3)
               (coe du34 v0 (coe du34 v0 v1 v3) v2)
               v3
               v3)
            (coe du118 v0 v3))
         (coe du154 v0 (coe du34 v0 (coe du34 v0 (coe du34 v0 v1 v3) v2) v3)
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               (coe du34 v0 v1 v3)
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  v2
                  v3))
            (coe du34 v0 (coe du34 v0 v1 v3) (coe du34 v0 v2 v3))
            (coe du40 v0 (coe du34 v0 v1 v3) v2 v3)
            (coe du152 v0
               (coe du34 v0 (coe du34 v0 v1 v3) (coe du34 v0 v2 v3)))))
name280 = "Algebra.RingSolver.Lemmas._.lem\8322"
d280 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du280 v4 v6 v7 v8 v9 v10
du280 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0
         (coe du34 v0 (coe du36 v0 (coe du34 v0 v1 v4) (coe du34 v0 v2 v3))
            v5)
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               (coe du34 v0 v1 v4)
               v5)
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               (coe du34 v0 v2 v3)
               v5))
         (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
            (coe du34 v0 v2 (coe du34 v0 v3 v5)))
         (coe MAlonzo.Code.Data.Product.d28 (coe du96 v0) v5
            (coe du34 v0 v1 v4)
            (coe du34 v0 v2 v3))
         (coe du154 v0
            (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v4) v5)
               (coe du34 v0 (coe du34 v0 v2 v3) v5))
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  v1
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v4
                     v5))
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  v2
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v3
                     v5)))
            (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
               (coe du34 v0 v2 (coe du34 v0 v3 v5)))
            (coe MAlonzo.Code.Function.du176 (coe du40 v0 v1 v4 v5)
               (coe du66 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v1
                        v4)
                     v5)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v1
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v4
                        v5))
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v2
                        v3)
                     v5)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v2
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v3
                        v5)))
               (coe du40 v0 v2 v3 v5))
            (coe du154 v0
               (coe du36 v0 (coe du34 v0 v1 (coe du34 v0 v4 v5))
                  (coe du34 v0 v2 (coe du34 v0 v3 v5)))
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     v1
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v5
                        v4))
                  (coe du34 v0 v2 (coe du34 v0 v3 v5)))
               (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
                  (coe du34 v0 v2 (coe du34 v0 v3 v5)))
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Function.du176 (coe du118 v0 v1)
                     (coe du46 v0 v1 v1
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                           v4
                           v5)
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                           v5
                           v4))
                     (coe du42 v0 v4 v5))
                  (coe du66 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v1
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                           v4
                           v5))
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        v1
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                           v5
                           v4))
                     (coe du34 v0 v2 (coe du34 v0 v3 v5))
                     (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                  (coe du118 v0 (coe du34 v0 v2 (coe du34 v0 v3 v5))))
               (coe du154 v0
                  (coe du36 v0 (coe du34 v0 v1 (coe du34 v0 v5 v4))
                     (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                           v1
                           v5)
                        v4)
                     (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                  (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
                     (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                  (coe MAlonzo.Code.Function.du158
                     (coe du126 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                                 v1
                                 v5)
                              v4)
                           (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                              v1
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                                 v5
                                 v4))
                           (coe du34 v0 v2 (coe du34 v0 v3 v5))))
                     (coe MAlonzo.Code.Function.du176 (coe du40 v0 v1 v5 v4)
                        (coe du66 v0
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                                 v1
                                 v5)
                              v4)
                           (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                              v1
                              (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                                 v5
                                 v4))
                           (coe du34 v0 v2 (coe du34 v0 v3 v5))
                           (coe du34 v0 v2 (coe du34 v0 v3 v5)))
                        (coe du118 v0 (coe du34 v0 v2 (coe du34 v0 v3 v5)))))
                  (coe du152 v0
                     (coe du36 v0 (coe du34 v0 (coe du34 v0 v1 v5) v4)
                        (coe du34 v0 v2 (coe du34 v0 v3 v5))))))))
name284 = "Algebra.RingSolver.Lemmas.lemma\8325"
d284 v0 v1 v2 v3 v4 v5 v6 = du284 v4 v6
du284 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0
         (coe du36 v0
            (coe du34 v0
               (coe du36 v0 (coe du34 v0 (coe du88 v0) v1) (coe du90 v0))
               v1)
            (coe du88 v0))
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
                  (coe du90 v0))
               v1)
            (coe du88 v0))
         v1
         (coe MAlonzo.Code.Function.du176
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Function.du176 (coe du132 v0 v1)
                  (coe du66 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
                        v1)
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
                     (coe du90 v0)
                     (coe du90 v0))
                  (coe du118 v0 (coe du90 v0)))
               (coe du46 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
                        v1)
                     (coe du90 v0))
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
                     (coe du90 v0))
                  v1
                  v1)
               (coe du118 v0 v1))
            (coe du66 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
                        v1)
                     (coe du90 v0))
                  v1)
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
                     (coe du90 v0))
                  v1)
               (coe du88 v0)
               (coe du88 v0))
            (coe du118 v0 (coe du88 v0)))
         (coe du154 v0
            (coe du36 v0
               (coe du34 v0 (coe du36 v0 (coe du88 v0) (coe du90 v0)) v1)
               (coe du88 v0))
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe du90 v0)
                  v1)
               (coe du88 v0))
            v1
            (coe MAlonzo.Code.Function.du176
               (coe MAlonzo.Code.Function.du176
                  (coe MAlonzo.Code.Data.Product.d26 (coe du68 v0) (coe du90 v0))
                  (coe du46 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
                        (coe du90 v0))
                     (coe du90 v0)
                     v1
                     v1)
                  (coe du118 v0 v1))
               (coe du66 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
                        (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
                        (coe du90 v0))
                     v1)
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                     (coe du90 v0)
                     v1)
                  (coe du88 v0)
                  (coe du88 v0))
               (coe du118 v0 (coe du88 v0)))
            (coe du154 v0
               (coe du36 v0 (coe du34 v0 (coe du90 v0) v1) (coe du88 v0))
               (coe du34 v0 (coe du90 v0) v1)
               v1
               (coe MAlonzo.Code.Data.Product.d28 (coe du68 v0)
                  (coe du34 v0 (coe du90 v0) v1))
               (coe du154 v0 (coe du34 v0 (coe du90 v0) v1) v1 v1
                  (coe MAlonzo.Code.Data.Product.d26 (coe du48 v0) v1)
                  (coe du152 v0 v1)))))
name292 = "Algebra.RingSolver.Lemmas.lemma\8326"
d292 v0 v1 v2 v3 v4 v5 v6 v7 = du292 v4 v6 v7
du292 v0 v1 v2
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0 (coe du36 v0 (coe du34 v0 (coe du88 v0) v2) v1)
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d164 v0
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
            v1)
         v1
         (coe MAlonzo.Code.Function.du176 (coe du132 v0 v2)
            (coe du66 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
                  v2)
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d170 v0)
               v1
               v1)
            (coe du118 v0 v1))
         (coe du154 v0 (coe du36 v0 (coe du88 v0) v1) v1 v1
            (coe MAlonzo.Code.Data.Product.d26 (coe du68 v0) v1)
            (coe du152 v0 v1)))
name300 = "Algebra.RingSolver.Lemmas.lemma\8327"
d300 v0 v1 v2 v3 v4 v5 v6 = du300 v4 v6
du300 v0 v1
  = coe MAlonzo.Code.Relation.Binary.PreorderReasoning.d62
      (coe du154 v0 (coe du34 v0 (coe du80 v0 (coe du90 v0)) v1)
         (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d168 v0
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
               (coe du90 v0)
               v1))
         (coe du80 v0 v1)
         (coe du82 v0 (coe du90 v0) v1)
         (coe du154 v0 (coe du80 v0 (coe du34 v0 (coe du90 v0) v1))
            (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d168 v0
               v1)
            (coe du80 v0 v1)
            (coe du86 v0
               (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d166 v0
                  (coe MAlonzo.Code.Algebra.RingSolver.AlmostCommutativeRing.d172 v0)
                  v1)
               v1
               (coe MAlonzo.Code.Data.Product.d26 (coe du48 v0) v1))
            (coe du152 v0 (coe du80 v0 v1))))