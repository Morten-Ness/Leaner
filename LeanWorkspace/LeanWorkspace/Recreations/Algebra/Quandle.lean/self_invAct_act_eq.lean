import Mathlib

variable {R : Type*} [Rack R]

theorem self_invAct_act_eq {x y : R} : (x ◃⁻¹ x) ◃ y = x ◃ y := by
  have h := @Rack.self_act_invAct_eq _ _ (op x) (op y)
  simpa using h

