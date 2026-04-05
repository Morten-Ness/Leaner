import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t := image_inter _ _ <| MulAction.injective₀ ha

