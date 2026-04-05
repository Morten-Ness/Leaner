import Mathlib

variable {G₀ G M α β : Type*}

variable [GroupWithZero α] [MulAction α β] {a : α}

theorem inv_smul_eq_iff₀ (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y := inv_smul_eq_iff (g := Units.mk0 a ha)

