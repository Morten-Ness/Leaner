import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

theorem map {F : Type*} [AddCommGroup F] [Module K F] (f : E ≃ₗ[K] F) :
    Submodule.map (f.restrictScalars ℤ : E →ₗ[ℤ] F) (span ℤ (Set.range b)) =
      span ℤ (Set.range (b.map f)) := by
  simp_rw [Submodule.map_span, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    Module.Basis.coe_map, Set.range_comp]

