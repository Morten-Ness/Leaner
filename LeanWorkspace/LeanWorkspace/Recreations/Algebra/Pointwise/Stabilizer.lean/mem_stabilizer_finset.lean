import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

variable [DecidableEq α]

theorem mem_stabilizer_finset {s : Finset α} : a ∈ stabilizer G s ↔ ∀ b, a • b ∈ s ↔ b ∈ s := by
  simp_rw [← MulAction.stabilizer_coe_finset, MulAction.mem_stabilizer_set, Finset.mem_coe]

