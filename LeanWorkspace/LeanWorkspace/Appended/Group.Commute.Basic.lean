import Mathlib

section

variable {G : Type*}

variable [Group G] {a b : G}

theorem inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b := by
  rw [← mul_assoc, h.inv_mul_cancel]

end
