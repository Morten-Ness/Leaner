import Mathlib

variable {G : Type*}

variable [Group G] {a b : G}

theorem inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b := by
  calc
    a⁻¹ * (b * a) = a⁻¹ * (a * b) := by rw [h.eq]
    _ = b := by simp [mul_assoc]
