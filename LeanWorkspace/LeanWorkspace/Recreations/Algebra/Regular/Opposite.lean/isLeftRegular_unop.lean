import Mathlib

variable {R} [Mul R]

theorem isLeftRegular_unop {a : Rᵐᵒᵖ} : IsLeftRegular a.unop ↔ IsRightRegular a := isRightRegular_op.symm

