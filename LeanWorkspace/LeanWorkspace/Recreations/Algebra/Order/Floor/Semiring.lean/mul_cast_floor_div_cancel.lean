import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem mul_cast_floor_div_cancel {n : ℕ} (hn : n ≠ 0) (a : R) : ⌊a * n⌋₊ / n = ⌊a⌋₊ := by
  rcases le_total a 0 with ha | ha
  · rw [Nat.floor_of_nonpos, Nat.floor_of_nonpos ha]
    · simp
    apply mul_nonpos_of_nonpos_of_nonneg ha n.cast_nonneg
  refine eq_of_forall_le_iff fun m ↦ ?_
  rw [le_div_iff_mul_le (zero_lt_of_ne_zero hn), le_floor_iff (mul_nonneg ha (cast_nonneg' n)),
    le_floor_iff ha, cast_mul, mul_le_mul_iff_of_pos_right (cast_pos'.mpr (zero_lt_of_ne_zero hn))]

