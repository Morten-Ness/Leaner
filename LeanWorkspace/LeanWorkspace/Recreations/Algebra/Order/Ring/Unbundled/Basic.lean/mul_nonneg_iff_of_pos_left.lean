import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_nonneg_iff_of_pos_left [PosMulStrictMono R]
    (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b := by
  convert mul_le_mul_iff_right₀ h
  simp

