import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

variable [DecidableEq α]

theorem mem_stabilizer_finset' {s : Finset α} : a ∈ stabilizer G s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← Subgroup.inv_mem_iff, MulAction.mem_stabilizer_finset_iff_subset_smul_finset]
  simp_rw [← Finset.mem_inv_smul_finset_iff, Finset.subset_iff]

