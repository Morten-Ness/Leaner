import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem zero_mem_resolventSet_of_unit (a : Aˣ) : 0 ∈ resolventSet R (a : A) := by
  simpa only [spectrum.mem_resolventSet_iff, ← spectrum.notMem_iff, spectrum.zero_notMem_iff] using a.isUnit

