import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem subset_smul_finset_iff : s ⊆ a • t ↔ a⁻¹ • s ⊆ t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.subset_smul_set_iff

