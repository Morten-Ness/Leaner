import Mathlib

variable {R} [Mul R]

theorem isLeftRegular_op {a : R} : IsLeftRegular (op a) ↔ IsRightRegular a := opEquiv.comp_injective _ |>.trans <| opEquiv.injective_comp _ |>.symm

