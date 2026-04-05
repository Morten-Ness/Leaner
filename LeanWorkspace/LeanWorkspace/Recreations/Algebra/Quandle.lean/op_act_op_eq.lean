import Mathlib

variable {R : Type*} [Rack R]

theorem op_act_op_eq {x y : R} : op x ◃ op y = op (x ◃⁻¹ y) := rfl

