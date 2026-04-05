import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A := show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff

