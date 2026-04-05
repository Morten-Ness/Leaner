import Mathlib

variable {R : Type*} [Rack R]

theorem self_act_act_eq {x y : R} : (x ◃ x) ◃ y = x ◃ y := by rw [← right_inv x y, ← self_distrib]

