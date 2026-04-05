import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem isCompl_ker_weight_span_coroot (α : Weight K H L) :
    IsCompl α.ker (K ∙ LieAlgebra.IsKilling.coroot α) := by
  if hα : α.IsZero then
    simpa [Weight.coe_toLinear_eq_zero_iff.mpr hα, coroot_eq_zero_iff.mpr hα, Weight.ker]
      using isCompl_top_bot
  else
    rw [← LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton]
    apply Module.Dual.isCompl_ker_of_disjoint_of_ne_bot (by simp_all)
      (LieAlgebra.IsKilling.disjoint_ker_weight_corootSpace α)
    replace hα : corootSpace α ≠ ⊥ := by simpa using hα
    rwa [ne_eq, ← LieSubmodule.toSubmodule_inj] at hα

