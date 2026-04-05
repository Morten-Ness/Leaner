import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeries_map_le (k : ℕ) : (derivedSeries R L' k).map f ≤ derivedSeries R L k := by
  induction k with
  | zero => simp only [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_zero, le_top]
  | succ k ih =>
    simp only [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ] at ih ⊢
    exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie ih ih)

