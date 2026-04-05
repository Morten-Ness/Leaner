import Mathlib

variable {R} [Mul R]

theorem isRightRegular_unop {a : Rᵐᵒᵖ} : IsRightRegular a.unop ↔ IsLeftRegular a := isLeftRegular_op.symm

