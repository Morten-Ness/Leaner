import Mathlib

variable {R : Type*} [Rack R]

theorem act'_symm_apply (x y : R) : (Rack.act' x).symm y = x ◃⁻¹ y := rfl

