import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

variable {s : Set α}

theorem mem_stabilizer_set_iff_smul_set_subset {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ a • s ⊆ s := by
  lift s to Finset α using hs
  classical
  rw [MulAction.stabilizer_coe_finset, MulAction.mem_stabilizer_finset_iff_smul_finset_subset, ← Finset.coe_smul_finset,
    Finset.coe_subset]

