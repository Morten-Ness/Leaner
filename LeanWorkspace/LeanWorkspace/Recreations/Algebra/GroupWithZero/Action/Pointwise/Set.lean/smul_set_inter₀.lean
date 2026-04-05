import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t := show Units.mk0 a ha • _ = _ from smul_set_inter

