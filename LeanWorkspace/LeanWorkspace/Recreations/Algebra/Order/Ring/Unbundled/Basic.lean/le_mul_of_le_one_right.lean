import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem le_mul_of_le_one_right [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (h : b ≤ 1) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

