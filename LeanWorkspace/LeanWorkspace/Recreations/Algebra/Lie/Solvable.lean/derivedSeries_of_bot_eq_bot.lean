import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeries_of_bot_eq_bot (k : ℕ) : LieAlgebra.derivedSeriesOfIdeal R L k ⊥ = ⊥ := by
  rw [eq_bot_iff]; exact LieAlgebra.derivedSeriesOfIdeal_le_self ⊥ k

