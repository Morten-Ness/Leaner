import Mathlib

variable {E ι : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

theorem fundamentalDomain_subset_parallelepiped [Fintype ι] :
    ZSpan.fundamentalDomain b ⊆ parallelepiped b := by
  rw [ZSpan.fundamentalDomain, parallelepiped_basis_eq, Set.setOf_subset_setOf]
  exact fun _ h i ↦ Set.Ico_subset_Icc_self (h i)

