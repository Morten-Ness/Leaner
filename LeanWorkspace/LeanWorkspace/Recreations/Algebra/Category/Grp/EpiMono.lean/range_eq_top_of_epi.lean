import Mathlib

open scoped Pointwise

variable {A B : CommGrpCat.{u}} (f : A ⟶ B)

theorem range_eq_top_of_epi [Epi f] : f.hom.range = ⊤ := MonoidHom.range_eq_top_of_cancel fun u v GrpCat.SurjectiveOfEpiAuxs.h => ConcreteCategory.ext_iff.mp <|
    (@cancel_epi _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 (ConcreteCategory.ext GrpCat.SurjectiveOfEpiAuxs.h)

