import Mathlib

variable {α : Type u}

variable [Monoid α] {a : α}

theorem divp_self (u : αˣ) : (u : α) /ₚ u = 1 := Units.mul_inv _

