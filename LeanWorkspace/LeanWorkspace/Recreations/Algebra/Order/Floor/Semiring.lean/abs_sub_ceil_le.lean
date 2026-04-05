import Mathlib

variable {R K : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

theorem abs_sub_ceil_le {a : R} (ha : 0 ≤ a) : |a - ⌈a⌉₊| ≤ 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (Nat.ceil_lt_add_one ha).le
  · simpa using (Nat.le_ceil a).trans (le_add_of_nonneg_left zero_le_one)

