import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] {a : R}

theorem natCast_mul_floor_div_cancel {n : ℕ} (hn : n ≠ 0) (a : R) : ⌊n * a⌋ / n = ⌊a⌋ := by
  rw [mul_comm, Int.mul_natCast_floor_div_cancel hn]

