import Mathlib

variable {R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K] {a b : K}

theorem div_two_lt_floor (ha : 1 ≤ a) : a / 2 < ⌊a⌋₊ := by
  rw [div_eq_inv_mul]; refine Nat.mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

