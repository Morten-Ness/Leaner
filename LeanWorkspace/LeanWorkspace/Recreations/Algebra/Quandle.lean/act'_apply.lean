import Mathlib

variable {R : Type*} [Rack R]

theorem act'_apply (x y : R) : Rack.act' x y = x ◃ y := rfl

