import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b := ⟨fun h ↦ by rw [← h, inv_mul_cancel_right], fun h ↦ by rw [h, mul_inv_cancel_right]⟩

