import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s := by
  rw [← Finset.smul_mem_smul_finset_iff a, smul_inv_smul]

