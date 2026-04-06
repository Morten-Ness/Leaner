import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_mem_smul_finset_iff (a : α) : a • b ∈ a • s ↔ b ∈ s := by
  simp [Finset.mem_smul_finset, smul_eq_iff_eq_inv_smul, inv_smul_smul]
