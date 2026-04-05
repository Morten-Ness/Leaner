import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s := by
  rw [← Finset.smul_mem_smul_finset_iff a, smul_inv_smul]

