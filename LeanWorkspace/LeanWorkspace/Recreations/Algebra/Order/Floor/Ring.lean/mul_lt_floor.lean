import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k] {a b : k}

theorem mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉ ≤ a) : b * a < ⌊a⌋ := by
  calc
    b * a < b * (⌊a⌋ + 1) := by gcongr; apply Int.lt_floor_add_one
    _ ≤ ⌊a⌋ := by
      rwa [_root_.mul_add_one, ← le_sub_iff_add_le', ← one_sub_mul, ← div_le_iff₀' (by linarith),
        ← ceil_le, le_floor]

