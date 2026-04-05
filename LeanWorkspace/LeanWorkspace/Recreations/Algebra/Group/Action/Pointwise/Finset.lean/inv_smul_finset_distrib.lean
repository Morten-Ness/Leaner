import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

variable [DecidableEq α]

theorem inv_smul_finset_distrib (a : α) (s : Finset α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  ext; simp [← Finset.inv_smul_mem_iff]

