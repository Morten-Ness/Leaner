import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable (R) [CommSemiring R]

theorem single_mem_gradeBy {R} [CommSemiring R] (f : M → ι) (m : M) (r : R) :
    single m r ∈ gradeBy R f (f m) := by
  intro x hx
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]

