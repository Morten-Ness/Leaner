import Mathlib

variable {R} [Mul R]

theorem isRegular_op {a : R} : IsRegular (op a) ↔ IsRegular a := by
  simp [isRegular_iff, and_comm]

