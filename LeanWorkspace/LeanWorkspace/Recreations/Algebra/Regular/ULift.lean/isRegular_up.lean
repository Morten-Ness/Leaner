import Mathlib

variable {α} {R : Type v}

variable [Mul R]

theorem isRegular_up {a : R} : IsRegular (ULift.up.{u} a) ↔ IsRegular a := by
  simp [isRegular_iff]

