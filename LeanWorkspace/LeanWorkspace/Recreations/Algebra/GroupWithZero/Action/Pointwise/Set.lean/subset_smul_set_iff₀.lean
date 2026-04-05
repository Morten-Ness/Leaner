import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem subset_smul_set_iff₀ (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B := show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_smul_set_iff

