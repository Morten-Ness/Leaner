import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t := image_diff (MulAction.injective₀ ha) _ _

