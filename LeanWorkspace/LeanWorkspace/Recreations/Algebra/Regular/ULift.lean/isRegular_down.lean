import Mathlib

variable {α} {R : Type v}

variable [Mul R]

theorem isRegular_down {a : ULift.{u} R} : IsRegular a.down ↔ IsRegular a := ULift.isRegular_up.symm

