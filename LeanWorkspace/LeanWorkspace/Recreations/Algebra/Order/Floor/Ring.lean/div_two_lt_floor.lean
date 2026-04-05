import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k] {a b : k}

theorem div_two_lt_floor (ha : 1 ≤ a) : a / 2 < ⌊a⌋ := by
  rw [div_eq_inv_mul]; refine Int.mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

