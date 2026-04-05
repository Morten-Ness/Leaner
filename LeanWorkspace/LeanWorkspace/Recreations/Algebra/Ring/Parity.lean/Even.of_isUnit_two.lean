import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Even.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Even a := let ⟨u, hu⟩ := h; ⟨u⁻¹ * a, by rw [← mul_add, ← two_mul, ← hu, Units.inv_mul_cancel_left]⟩

