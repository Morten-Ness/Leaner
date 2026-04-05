import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable (R) [CommSemiring R]

theorem mem_grade_iff (m : M) (a : R[M]) : a ∈ grade R m ↔ a.support ⊆ {m} := by
  rw [← Finset.coe_subset, Finset.coe_singleton]
  rfl

