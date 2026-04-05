import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeries_succ_eq_top_iff (n : ℕ) :
    derivedSeries R L (n + 1) = ⊤ ↔ derivedSeries R L 1 = ⊤ := by
  simp only [LieAlgebra.derivedSeries_def]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [LieAlgebra.derivedSeriesOfIdeal_succ]
    refine ⟨fun h ↦ ?_, fun h ↦ by rwa [ih.mpr h]⟩
    rw [← ih, eq_top_iff]
    conv_lhs => rw [← h]
    exact LieSubmodule.lie_le_right _ _

