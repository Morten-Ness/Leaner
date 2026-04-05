import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeries_eq_derivedSeriesOfIdeal_comap (k : ℕ) :
    derivedSeries R I k = (LieAlgebra.derivedSeriesOfIdeal R L k I).comap I.incl := by
  induction k with
  | zero => simp only [LieAlgebra.derivedSeries_def, comap_incl_self, LieAlgebra.derivedSeriesOfIdeal_zero]
  | succ k ih =>
    simp only [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ] at ih ⊢; rw [ih]
    exact comap_bracket_incl_of_le I (LieAlgebra.derivedSeriesOfIdeal_le_self I k)
      (LieAlgebra.derivedSeriesOfIdeal_le_self I k)

