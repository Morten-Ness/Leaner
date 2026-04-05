import Mathlib

variable {Q : Type*} [Quandle Q]

theorem fix_inv {x : Q} : x ◃⁻¹ x = x := by
  rw [← Rack.left_cancel x]
  simp

