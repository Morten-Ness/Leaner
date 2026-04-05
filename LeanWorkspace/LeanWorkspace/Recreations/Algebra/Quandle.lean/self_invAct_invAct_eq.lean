import Mathlib

variable {R : Type*} [Rack R]

theorem self_invAct_invAct_eq {x y : R} : (x ◃⁻¹ x) ◃⁻¹ y = x ◃⁻¹ y := by
  have h := @Rack.self_act_act_eq _ _ (op x) (op y)
  simpa using h

