import Mathlib

variable {G₀ G M α β : Type*}

variable [GroupWithZero α] [MulAction α β] {a : α}

theorem smul_inv_smul₀ (ha : a ≠ 0) (x : β) : a • a⁻¹ • x = x := smul_inv_smul (Units.mk0 a ha) x

