import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_subset_smul_set_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B := show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_set_subset_smul_set_iff

