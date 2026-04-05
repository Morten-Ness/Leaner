import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] {a : R}

theorem cast_mul_floor_div_cancel_of_pos {n : ℤ} (hn : 0 < n) (a : R) : ⌊n * a⌋ / n = ⌊a⌋ := by
  rw [mul_comm, Int.mul_cast_floor_div_cancel_of_pos hn]

