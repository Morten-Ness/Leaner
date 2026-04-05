import Mathlib

variable {G M S : Type*}

variable [Group G] {a b : G}

theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, Commute.mul_inv_cancel h]

