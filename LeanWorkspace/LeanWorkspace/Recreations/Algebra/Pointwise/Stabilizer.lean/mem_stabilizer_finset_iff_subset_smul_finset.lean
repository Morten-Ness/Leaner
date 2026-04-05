import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

variable [DecidableEq α]

theorem mem_stabilizer_finset_iff_subset_smul_finset {s : Finset α} :
    a ∈ stabilizer G s ↔ s ⊆ a • s := by
  rw [mem_stabilizer_iff, Finset.subset_iff_eq_of_card_le (Finset.card_smul_finset _ _).le, eq_comm]

