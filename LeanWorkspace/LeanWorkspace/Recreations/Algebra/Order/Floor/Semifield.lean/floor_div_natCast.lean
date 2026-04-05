import Mathlib

variable {R K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

theorem floor_div_natCast (a : K) (n : ℕ) : ⌊a / n⌋₊ = ⌊a⌋₊ / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  nth_rw 2 [← div_mul_cancel₀ (a := a) (b := ↑n) (by positivity)]
  rw [mul_cast_floor_div_cancel (Nat.ne_zero_of_lt hn)]

