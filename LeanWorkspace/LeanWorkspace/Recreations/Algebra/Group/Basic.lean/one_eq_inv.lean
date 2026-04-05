import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 := eq_comm.trans inv_eq_one

