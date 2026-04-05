import Mathlib

open scoped Pointwise

variable {A B : CommGrpCat.{u}} (f : A ⟶ B)

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [CommGrpCat.epi_iff_range_eq_top, MonoidHom.range_eq_top]

