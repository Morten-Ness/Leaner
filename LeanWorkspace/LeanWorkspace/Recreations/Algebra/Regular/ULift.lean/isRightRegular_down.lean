import Mathlib

variable {α} {R : Type v}

variable [Mul R]

theorem isRightRegular_down {a : ULift.{u} R} : IsRightRegular a.down ↔ IsRightRegular a := ULift.isRightRegular_up.symm

