import Mathlib

open scoped Pointwise symmDiff

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) := image_symmDiff (MulAction.injective₀ ha) _ _

