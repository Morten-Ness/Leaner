import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem subset_smul_finset_iff₀ (ha : a ≠ 0) : s ⊆ a • t ↔ a⁻¹ • s ⊆ t := show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_smul_finset_iff

