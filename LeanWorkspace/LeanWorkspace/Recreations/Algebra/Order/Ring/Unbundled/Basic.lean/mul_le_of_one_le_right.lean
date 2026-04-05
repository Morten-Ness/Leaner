import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem mul_le_of_one_le_right [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (h : 1 ≤ b) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

