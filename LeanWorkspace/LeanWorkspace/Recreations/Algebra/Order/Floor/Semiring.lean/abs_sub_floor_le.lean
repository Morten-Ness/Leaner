import Mathlib

variable {R K : Type*}

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

theorem abs_sub_floor_le {a : R} (ha : 0 ≤ a) : |a - ⌊a⌋₊| ≤ 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (Nat.floor_le ha).trans (le_add_of_nonneg_right zero_le_one)
  · simpa [add_comm] using (Nat.lt_floor_add_one a).le

