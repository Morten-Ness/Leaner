import Mathlib

variable {α} {R : Type v}

variable [Mul R]

theorem isRightRegular_up {a : R} : IsRightRegular (ULift.up.{u} a) ↔ IsRightRegular a := Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

