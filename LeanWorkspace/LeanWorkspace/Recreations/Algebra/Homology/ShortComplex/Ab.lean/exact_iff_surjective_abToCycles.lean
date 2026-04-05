import Mathlib

variable (S : ShortComplex Ab.{u})

theorem exact_iff_surjective_abToCycles :
    S.Exact ↔ Function.Surjective S.abToCycles := by
  rw [S.abLeftHomologyData.exact_iff_epi_f', CategoryTheory.ShortComplex.abLeftHomologyData_f',
    AddCommGrpCat.epi_iff_surjective]
  rfl

