import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

variable {s : Set α}

theorem mem_stabilizer_set' {s : Set α} (hs : s.Finite) :
    a ∈ stabilizer G s ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  lift s to Finset α using hs
  classical simp [-mem_stabilizer_iff, MulAction.mem_stabilizer_finset']

