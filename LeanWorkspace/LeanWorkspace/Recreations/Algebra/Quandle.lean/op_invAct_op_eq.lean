import Mathlib

variable {R : Type*} [Rack R]

theorem op_invAct_op_eq {x y : R} : op x ◃⁻¹ op y = op (x ◃ y) := rfl

