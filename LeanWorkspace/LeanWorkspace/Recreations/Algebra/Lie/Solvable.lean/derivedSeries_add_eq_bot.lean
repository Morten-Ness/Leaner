import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeries_add_eq_bot {k l : ℕ} {I J : LieIdeal R L} (hI : derivedSeries R I k = ⊥)
    (hJ : derivedSeries R J l = ⊥) : derivedSeries R (I + J) (k + l) = ⊥ := by
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hI hJ ⊢
  rw [← le_bot_iff]
  let D := LieAlgebra.derivedSeriesOfIdeal R L; change D k I = ⊥ at hI; change D l J = ⊥ at hJ
  calc
    D (k + l) (I + J) ≤ D k I + D l J := LieAlgebra.derivedSeriesOfIdeal_add_le_add I J k l
    _ ≤ ⊥ := by rw [hI, hJ]; simp

