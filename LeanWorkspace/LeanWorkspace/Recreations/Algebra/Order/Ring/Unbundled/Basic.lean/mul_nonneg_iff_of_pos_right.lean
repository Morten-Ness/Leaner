import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_nonneg_iff_of_pos_right [MulPosStrictMono R]
    (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b := by
  simpa using (mul_le_mul_iff_left₀ h : 0 * c ≤ b * c ↔ 0 ≤ b)

