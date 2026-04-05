import Mathlib

variable {R} [Mul R]

theorem isRightRegular_op {a : R} : IsRightRegular (op a) ↔ IsLeftRegular a := opEquiv.comp_injective _ |>.trans <| opEquiv.injective_comp _ |>.symm

