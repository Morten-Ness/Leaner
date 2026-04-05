import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_subset_smul_finset_iff₀ (ha : a ≠ 0) : a • s ⊆ a • t ↔ s ⊆ t := show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_smul_finset_iff

