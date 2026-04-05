import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 := inv_injective.eq_iff' inv_one

