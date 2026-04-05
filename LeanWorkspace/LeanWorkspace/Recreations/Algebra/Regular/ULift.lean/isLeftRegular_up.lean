import Mathlib

variable {α} {R : Type v}

variable [Mul R]

theorem isLeftRegular_up {a : R} : IsLeftRegular (ULift.up.{u} a) ↔ IsLeftRegular a := Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

