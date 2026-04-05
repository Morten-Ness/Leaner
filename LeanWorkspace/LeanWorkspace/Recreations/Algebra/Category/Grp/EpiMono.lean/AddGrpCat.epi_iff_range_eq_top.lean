import Mathlib

open scoped Pointwise

variable {A B : AddGrpCat.{u}} (f : A ⟶ B)

theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ := Iff.trans (AddGrpCat.epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.hom.range).symm

