import Mathlib

variable {R : Type*} [Rack R]

theorem assoc_iff_id {R : Type*} [Rack R] {x y z : R} : x ◃ y ◃ z = (x ◃ y) ◃ z ↔ x ◃ z = z := by
  rw [self_distrib]
  rw [Rack.left_cancel]

