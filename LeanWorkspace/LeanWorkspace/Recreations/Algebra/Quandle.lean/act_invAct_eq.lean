import Mathlib

variable {R : Type*} [Rack R]

theorem act_invAct_eq (x y : R) : x ◃ x ◃⁻¹ y = y := right_inv x y

