import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] {a b : R}

theorem mul_cast_floor_div_cancel_of_pos {n : ℤ} (hn : 0 < n) (a : R) : ⌊a * n⌋ / n = ⌊a⌋ := by
  refine eq_of_forall_le_iff fun m ↦ ?_
  rw [Int.le_ediv_iff_mul_le hn, le_floor, le_floor, cast_mul,
    mul_le_mul_iff_of_pos_right (cast_pos.mpr hn)]

