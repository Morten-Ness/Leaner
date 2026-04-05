import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

variable {s : Set G}

theorem stabilizer_subset_div_right (ha : a ∈ s) : ↑(stabilizer G s) ⊆ s / {a} := fun b hb ↦
  ⟨_, by rwa [← smul_eq_mul, MulAction.mem_stabilizer_set.1 hb], _, mem_singleton _, mul_div_cancel_right _ _⟩

