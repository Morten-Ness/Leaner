import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

set_option backward.isDefEq.respectTransparency false in
theorem exact_iff_surjective_moduleCatToCycles :
    S.Exact ↔ Function.Surjective S.moduleCatToCycles := by
  simp [S.moduleCatLeftHomologyData.exact_iff_epi_f',
    ModuleCat.epi_iff_surjective, moduleCatLeftHomologyData_K]

