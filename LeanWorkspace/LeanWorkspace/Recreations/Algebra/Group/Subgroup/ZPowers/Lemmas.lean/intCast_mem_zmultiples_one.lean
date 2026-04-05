import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {R : Type*} [Ring R] (r : R) (k : ℤ)

theorem intCast_mem_zmultiples_one : ↑(k : ℤ) ∈ zmultiples (1 : R) := mem_zmultiples_iff.mp ⟨k, by simp⟩

