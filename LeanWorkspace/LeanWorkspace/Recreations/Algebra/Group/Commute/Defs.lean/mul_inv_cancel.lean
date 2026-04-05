import Mathlib

variable {G M S : Type*}

variable [Group G] {a b : G}

theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [Commute.eq h, mul_inv_cancel_right]

