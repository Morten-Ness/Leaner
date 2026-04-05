import Mathlib

open scoped Pointwise Ring

variable {𝕜 : Type u} {A : Type v}

variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem zero_eq [Nontrivial A] : σ (0 : A) = {0} := by
  refine Set.Subset.antisymm ?_ (by simp [Algebra.algebraMap_eq_smul_one, spectrum.mem_iff])
  rw [spectrum, Set.compl_subset_comm]
  intro k hk
  rw [Set.mem_compl_singleton_iff] at hk
  have : IsUnit (Units.mk0 k hk • (1 : A)) := IsUnit.smul (Units.mk0 k hk) isUnit_one
  simpa [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]

