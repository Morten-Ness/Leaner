import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeries_eq_derivedSeriesOfIdeal_map (k : ℕ) :
    (derivedSeries R I k).map I.incl = LieAlgebra.derivedSeriesOfIdeal R L k I := by
  rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap, map_comap_incl, inf_eq_right]
  apply LieAlgebra.derivedSeriesOfIdeal_le_self

