import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem epi_iff_range_eq_top : Epi f ↔ f.hom.range = ⊤ := Iff.trans (GrpCat.epi_iff_surjective _) (Subgroup.eq_top_iff' f.hom.range).symm

