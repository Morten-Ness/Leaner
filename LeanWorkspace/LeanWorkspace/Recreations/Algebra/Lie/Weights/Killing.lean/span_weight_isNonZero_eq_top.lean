import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

theorem span_weight_isNonZero_eq_top :
    span K ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) = ⊤ := by
  rw [← LieAlgebra.IsKilling.span_weight_eq_top]
  refine le_antisymm (Submodule.span_mono <| by simp) ?_
  suffices Set.range (Weight.toLinear K H L) ⊆
    insert 0 ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) by
    simpa only [Submodule.span_insert_zero] using Submodule.span_mono this
  rintro - ⟨α, rfl⟩
  simp only [mem_insert_iff, Weight.coe_toLinear_eq_zero_iff, mem_image, mem_setOf_eq]
  tauto

