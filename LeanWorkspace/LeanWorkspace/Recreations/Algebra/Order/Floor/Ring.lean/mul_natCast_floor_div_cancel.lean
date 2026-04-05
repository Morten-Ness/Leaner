import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] {a b : R}

theorem mul_natCast_floor_div_cancel {n : ℕ} (hn : n ≠ 0) (a : R) : ⌊a * n⌋ / n = ⌊a⌋ := by
  simpa using Int.mul_cast_floor_div_cancel_of_pos (n := n) (by positivity) a

