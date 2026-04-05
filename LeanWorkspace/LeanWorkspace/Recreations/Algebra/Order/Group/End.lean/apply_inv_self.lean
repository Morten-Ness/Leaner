import Mathlib

variable {α : Type*} {r : α → α → Prop}

theorem apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x := e.apply_symm_apply x

