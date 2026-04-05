import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b := ⟨fun h ↦ by rw [h, inv_mul_cancel_right], fun h ↦ by rw [← h, mul_inv_cancel_right]⟩

