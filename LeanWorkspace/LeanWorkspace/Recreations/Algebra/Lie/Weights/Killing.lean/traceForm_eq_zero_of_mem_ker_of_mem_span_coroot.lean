import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem traceForm_eq_zero_of_mem_ker_of_mem_span_coroot {α : Weight K H L} {x y : H}
    (hx : x ∈ α.ker) (hy : y ∈ K ∙ LieAlgebra.IsKilling.coroot α) :
    traceForm K H L x y = 0 := by
  rw [← LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton, LieSubmodule.mem_toSubmodule, mem_corootSpace'] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, v, -, huv⟩ := hz
    change killingForm K L (x : L) (z : L) = 0
    replace hx : α x = 0 := by simpa using hx
    rw [← huv, ← traceForm_apply_lie_apply, ← LieSubalgebra.coe_bracket_of_module,
      LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace hu, hx, zero_smul, map_zero, LinearMap.zero_apply]
  | zero => simp
  | add _ _ _ _ hx hy => simp [hx, hy]
  | smul _ _ _ hz => simp [hz]

