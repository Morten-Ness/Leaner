import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ := ⟨eq_inv_of_mul_eq_one_left, fun h ↦ by rw [h, inv_mul_cancel]⟩

