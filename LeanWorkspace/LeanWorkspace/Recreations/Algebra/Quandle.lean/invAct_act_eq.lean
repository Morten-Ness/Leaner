import Mathlib

variable {R : Type*} [Rack R]

theorem invAct_act_eq (x y : R) : x ◃⁻¹ x ◃ y = y := left_inv x y

