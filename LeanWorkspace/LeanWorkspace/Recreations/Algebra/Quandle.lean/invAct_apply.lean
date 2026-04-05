import Mathlib

variable {R : Type*} [Rack R]

theorem invAct_apply (x y : R) : (Rack.act' x)⁻¹ y = x ◃⁻¹ y := rfl

