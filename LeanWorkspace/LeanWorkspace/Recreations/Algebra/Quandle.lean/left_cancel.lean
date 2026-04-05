import Mathlib

variable {R : Type*} [Rack R]

theorem left_cancel (x : R) {y y' : R} : x ◃ y = x ◃ y' ↔ y = y' := by
  constructor
  · apply (Rack.act' x).injective
  rintro rfl
  rfl

