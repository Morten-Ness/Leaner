import Mathlib

variable {R : Type*} [Rack R]

theorem self_invAct_eq_iff_eq {x y : R} : x ◃⁻¹ x = y ◃⁻¹ y ↔ x = y := by
  have h := @Rack.self_act_eq_iff_eq _ _ (op x) (op y)
  simpa using h

