import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_neg {x : R} (hx : fract x ≠ 0) : fract (-x) = 1 - fract x := by
  rw [Int.fract_eq_iff]
  constructor
  · rw [le_sub_iff_add_le, zero_add]
    exact (Int.fract_lt_one x).le
  refine ⟨sub_lt_self _ (lt_of_le_of_ne' (Int.fract_nonneg x) hx), -⌊x⌋ - 1, ?_⟩
  simp only [sub_sub_eq_add_sub, cast_sub, cast_neg, cast_one, sub_left_inj]
  conv in -x => rw [← Int.floor_add_fract x]
  simp [-Int.floor_add_fract]

