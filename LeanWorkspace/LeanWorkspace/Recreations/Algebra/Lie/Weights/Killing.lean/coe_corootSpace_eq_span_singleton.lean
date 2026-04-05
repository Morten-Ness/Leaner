import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem coe_corootSpace_eq_span_singleton (α : Weight K H L) :
    (corootSpace α).toSubmodule = K ∙ LieAlgebra.IsKilling.coroot α := by
  if hα : α.IsZero then
    simp [hα.eq, coroot_eq_zero_iff.mpr hα]
  else
    set α' := (LieAlgebra.IsKilling.cartanEquivDual H).symm α
    suffices (K ∙ LieAlgebra.IsKilling.coroot α) = K ∙ α' by rw [LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton']; exact this.symm
    have : IsUnit (2 * (α α')⁻¹) := by simpa using LieAlgebra.IsKilling.root_apply_cartanEquivDual_symm_ne_zero hα
    change (K ∙ (2 • (α α')⁻¹ • α')) = _
    simpa [← Nat.cast_smul_eq_nsmul K, smul_smul] using Submodule.span_singleton_smul_eq this _

