import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeries_eq_bot_iff (k : ℕ) :
    derivedSeries R I k = ⊥ ↔ LieAlgebra.derivedSeriesOfIdeal R L k I = ⊥ := by
  rw [← LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_map, map_eq_bot_iff, ker_incl, eq_bot_iff]

