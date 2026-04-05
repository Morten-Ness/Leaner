import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem inv_div : (a / b)⁻¹ = b / a := by simp

