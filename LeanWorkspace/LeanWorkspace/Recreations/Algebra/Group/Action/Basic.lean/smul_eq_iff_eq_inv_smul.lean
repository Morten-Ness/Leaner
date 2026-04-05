import Mathlib

variable {G M A B α β : Type*}

variable [Group α] [MulAction α β]

theorem smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g • x = y ↔ x = g⁻¹ • y := (MulAction.toPerm g).apply_eq_iff_eq_symm_apply

