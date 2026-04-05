import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_subset_iff : a • s ⊆ t ↔ s ⊆ a⁻¹ • t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.smul_set_subset_iff_subset_inv_smul_set

