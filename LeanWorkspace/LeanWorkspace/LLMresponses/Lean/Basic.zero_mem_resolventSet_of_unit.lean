import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem zero_mem_resolventSet_of_unit (a : Aˣ) : 0 ∈ resolventSet R (a : A) := by
  change IsUnit (algebraMap R A 0 - (a : A))
  simpa using (show IsUnit (-(a : A)) from isUnit_neg.mpr a.isUnit)
