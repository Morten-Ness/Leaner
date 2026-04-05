import Mathlib

open scoped Pointwise RightActions

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

variable {s : Set G}

theorem op_smul_set_stabilizer_subset (ha : a ∈ s) : (stabilizer G s : Set G) <• a ⊆ s := smul_set_subset_iff.2 fun b hb ↦ by rw [← hb]; exact smul_mem_smul_set ha

