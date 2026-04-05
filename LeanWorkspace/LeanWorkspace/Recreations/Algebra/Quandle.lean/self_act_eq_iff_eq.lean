import Mathlib

variable {R : Type*} [Rack R]

theorem self_act_eq_iff_eq {x y : R} : x ◃ x = y ◃ y ↔ x = y := by
  constructor; swap
  · rintro rfl; rfl
  intro h
  trans (x ◃ x) ◃⁻¹ x ◃ x
  · rw [← Rack.left_cancel (x ◃ x), right_inv, Rack.self_act_act_eq]
  · rw [h, ← Rack.left_cancel (y ◃ y), right_inv, Rack.self_act_act_eq]

