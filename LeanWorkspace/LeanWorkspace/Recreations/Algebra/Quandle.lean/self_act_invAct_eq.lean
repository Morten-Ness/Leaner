import Mathlib

variable {R : Type*} [Rack R]

theorem self_act_invAct_eq {x y : R} : (x ◃ x) ◃⁻¹ y = x ◃⁻¹ y := by
  rw [← Rack.left_cancel (x ◃ x)]
  rw [right_inv]
  rw [Rack.self_act_act_eq]
  rw [right_inv]

