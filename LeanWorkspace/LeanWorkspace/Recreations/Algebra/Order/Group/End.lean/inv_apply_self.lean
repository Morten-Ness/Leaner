import Mathlib

variable {α : Type*} {r : α → α → Prop}

theorem inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x := e.symm_apply_apply x

