import Mathlib

open scoped Pointwise symmDiff

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) := image_symmDiff _ _ <| MulAction.injective₀ ha

