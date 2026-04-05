import Mathlib

variable {R : Type*} [Rack R]

theorem left_cancel_inv (x : R) {y y' : R} : x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y' := by
  constructor
  · apply (Rack.act' x).symm.injective
  rintro rfl
  rfl

