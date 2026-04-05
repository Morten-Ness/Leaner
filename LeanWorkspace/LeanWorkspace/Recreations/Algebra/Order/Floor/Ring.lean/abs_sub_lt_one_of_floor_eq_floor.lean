import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem abs_sub_lt_one_of_floor_eq_floor {a b : R} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 := by
  wlog h0 : b ≤ a generalizing a b
  · rw [abs_sub_comm]
    exact this h.symm (le_of_not_ge h0)
  calc |a - b|
    _ = a - b := abs_of_nonneg (sub_nonneg_of_le h0)
    _ < ⌊a⌋ + 1 - b := sub_lt_sub_right (Int.lt_floor_add_one a) _
    _ ≤ ⌊a⌋ + 1 - ⌊b⌋ := sub_le_sub_left (floor_le b) _
    _ = 1 := by rw [h, add_sub_cancel_left]

