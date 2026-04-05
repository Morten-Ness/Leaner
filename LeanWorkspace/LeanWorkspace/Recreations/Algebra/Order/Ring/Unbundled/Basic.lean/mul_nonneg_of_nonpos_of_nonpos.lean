import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem mul_nonneg_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb

