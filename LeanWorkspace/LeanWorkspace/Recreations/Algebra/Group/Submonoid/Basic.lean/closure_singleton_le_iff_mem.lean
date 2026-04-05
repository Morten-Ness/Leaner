import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_singleton_le_iff_mem (m : M) (p : Submonoid M) : Submonoid.closure {m} ≤ p ↔ m ∈ p := by
  rw [Submonoid.closure_le, singleton_subset_iff, SetLike.mem_coe]

