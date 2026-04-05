import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_univ₀ [Fintype β] (ha : a ≠ 0) : a • (univ : Finset β) = univ := coe_injective <| by push_cast; exact Set.smul_set_univ₀ ha

