import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem lieCharacter_apply_of_mem_derived (χ : LieCharacter R L) {x : L}
    (h : x ∈ derivedSeries R L 1) : χ x = 0 := by
  rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, ←
    LieSubmodule.mem_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span] at h
  induction h using Submodule.span_induction with
  | mem y h =>
    simp only [Subtype.exists, LieSubmodule.mem_top, exists_const, Set.mem_setOf_eq] at h
    obtain ⟨z, w, rfl⟩ := h
    exact LieAlgebra.lieCharacter_apply_lie ..
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul t y _ hy => rw [map_smul, hy, smul_zero]

