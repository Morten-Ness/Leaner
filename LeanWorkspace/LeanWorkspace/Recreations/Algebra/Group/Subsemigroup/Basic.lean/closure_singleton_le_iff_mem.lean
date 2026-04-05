import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem closure_singleton_le_iff_mem (m : M) (p : Subsemigroup M) : Subsemigroup.closure {m} ≤ p ↔ m ∈ p := by
  rw [Subsemigroup.closure_le, singleton_subset_iff, SetLike.mem_coe]

