import Mathlib

variable {α} {R : Type v}

variable [Mul R]

theorem isLeftRegular_down {a : ULift.{u} R} : IsLeftRegular a.down ↔ IsLeftRegular a := ULift.isLeftRegular_up.symm

