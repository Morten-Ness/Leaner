import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem mul_le_of_one_le_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hb : b ≤ 0) (h : 1 ≤ a) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

