import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k] {a b : k}

theorem floor_div_cast_of_nonneg {n : ℤ} (hn : 0 ≤ n) (a : k) : ⌊a / n⌋ = ⌊a⌋ / n := by
  obtain rfl | hn := hn.eq_or_lt
  · simp
  nth_rw 2 [← div_mul_cancel₀ (a := a) (ne_of_gt (Int.cast_pos.mpr hn))]
  rw [Int.mul_cast_floor_div_cancel_of_pos hn]

