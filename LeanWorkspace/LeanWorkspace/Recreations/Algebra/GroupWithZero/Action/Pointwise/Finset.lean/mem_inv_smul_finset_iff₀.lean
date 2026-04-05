import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem mem_inv_smul_finset_iff₀ (ha : a ≠ 0) : b ∈ a⁻¹ • s ↔ a • b ∈ s := show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_finset_iff

