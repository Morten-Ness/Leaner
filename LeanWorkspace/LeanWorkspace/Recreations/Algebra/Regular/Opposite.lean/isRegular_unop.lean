import Mathlib

variable {R} [Mul R]

theorem isRegular_unop {a : Rᵐᵒᵖ} : IsRegular a.unop ↔ IsRegular a := isRegular_op.symm

