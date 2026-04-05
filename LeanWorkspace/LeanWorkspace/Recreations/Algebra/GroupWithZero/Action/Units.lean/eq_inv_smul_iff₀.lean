import Mathlib

variable {G₀ G M α β : Type*}

variable [GroupWithZero α] [MulAction α β] {a : α}

theorem eq_inv_smul_iff₀ (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y := eq_inv_smul_iff (g := Units.mk0 a ha)

