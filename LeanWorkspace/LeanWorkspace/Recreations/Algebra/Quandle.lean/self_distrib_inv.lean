import Mathlib

variable {R : Type*} [Rack R]

theorem self_distrib_inv {x y z : R} : x ◃⁻¹ y ◃⁻¹ z = (x ◃⁻¹ y) ◃⁻¹ x ◃⁻¹ z := by
  rw [← Rack.left_cancel (x ◃⁻¹ y), right_inv, ← Rack.left_cancel x, right_inv, self_distrib]
  repeat' rw [right_inv]

