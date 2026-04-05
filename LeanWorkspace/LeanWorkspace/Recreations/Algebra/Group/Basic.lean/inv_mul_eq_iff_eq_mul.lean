import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c := ⟨fun h ↦ by rw [← h, mul_inv_cancel_left], fun h ↦ by rw [h, inv_mul_cancel_left]⟩

