import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_mem_smul_finset_iff (a : α) : a • b ∈ a • s ↔ b ∈ s := (MulAction.injective _).mem_finset_image

