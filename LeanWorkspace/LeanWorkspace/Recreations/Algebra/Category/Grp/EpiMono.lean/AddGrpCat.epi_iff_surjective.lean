import Mathlib

open scoped Pointwise

variable {A B : AddGrpCat.{u}} (f : A ⟶ B)

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  have i1 : Epi f ↔ Epi (groupAddGroupEquivalence.inverse.map f) := by
    refine ⟨?_, groupAddGroupEquivalence.inverse.epi_of_epi_map⟩
    apply groupAddGroupEquivalence.inverse.map_epi
  rwa [GrpCat.epi_iff_surjective] at i1

